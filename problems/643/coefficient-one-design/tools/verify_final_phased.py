#!/usr/bin/env python3
"""Resumable, exact-source final check. Invoke each phase with an outer 240-second cap."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib
from datetime import datetime, timezone

from verify_endpoint import closure, checked_run, sha
from design_scope import load_scope
SCOPE = load_scope(Path(__file__).resolve().parents[1])
TARGET = SCOPE["target"]
AXIOM_MODULES = SCOPE["declarations"]
AXIOM_THEOREMS = list(AXIOM_MODULES)
from runtime import discover

ROOT = Path(__file__).resolve().parents[1]
LEAN = LEANCHECKER = PACKAGES = None
BUILD = ROOT / '.verified-final'
RECEIPTS = ROOT / 'receipts'
STATE = RECEIPTS / 'final-state.json'
SUCCESS = RECEIPTS / 'final-receipt.json'
FAILURE = RECEIPTS / 'final-failure.json'
CHUNK = 1
KERNEL_CHUNK = 1
INPUTS = [
    'check.sh', 'tools/verify_final_phased.py', 'tools/verify_endpoint.py',
    'tools/test_failure_control.py', 'tools/Hygiene.lean', 'tools/srcscan.py',
    'tools/olean_pins.py', 'tools/toolchain_pins.py', 'tools/runtime.py', 'tools/run_phase.py',
    'tools/bounded_process.py', 'tools/design_scope.py', 'design-scope.json',
    'COPYING', 'licenses/Sage-COPYING.txt', 'NOTICE-DESIGN.md', 'design-source-provenance.json',
    'source-manifest.json', 'new-source-manifest.json',
    'upstream-source-manifest.json', 'LICENSE.upstream',
    'lake-manifest.json', 'standalone/lake-manifest.json',
    'lakefile.toml', 'lean-toolchain',
    'pins/package-oleans.sha256', 'pins/toolchain.sha256',
]


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def git_state(name):
    try:
        rev = subprocess.run(['git', '-C', str(PACKAGES / name), 'rev-parse', 'HEAD'],
                             check=True, capture_output=True, text=True, timeout=240).stdout.strip()
        dirty = subprocess.run(['git', '-C', str(PACKAGES / name), 'status', '--porcelain',
                                '--untracked-files=no'], check=True, capture_output=True,
                               text=True, timeout=240).stdout.strip()
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f'UNKNOWN timeout 240s: git package check {name}') from exc
    return rev, dirty


def package_manifest():
    root = ROOT / 'lake-manifest.json'
    other = ROOT / 'standalone/lake-manifest.json'
    if root.read_bytes() != other.read_bytes():
        raise RuntimeError('root and standalone package manifests differ')
    data = json.loads(root.read_text())
    lakefile = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    mathlib = [p for p in data['packages'] if p['name'] == 'mathlib']
    requires = [p for p in lakefile['require'] if p['name'] == 'mathlib']
    if len(mathlib) != 1 or len(requires) != 1 or mathlib[0]['rev'] != requires[0]['rev']:
        raise RuntimeError('lakefile Mathlib pin differs from lake-manifest')
    return data


def current_sources():
    old = json.loads((ROOT / 'source-manifest.json').read_text())
    new = json.loads((ROOT / 'new-source-manifest.json').read_text())
    upstream = json.loads((ROOT / 'upstream-source-manifest.json').read_text())
    if set(old) & set(new) or (set(old) | set(new)) & set(upstream['files']):
        raise RuntimeError('source manifests overlap')
    if sha(ROOT / 'LICENSE.upstream') != upstream['license_sha256']:
        raise RuntimeError('upstream license changed')
    pinned = old | new | upstream['files']
    for rel, expected in pinned.items():
        if sha(ROOT / rel) != expected:
            raise RuntimeError(f'source changed: {rel}')
    return pinned


def environment(state):
    env = os.environ.copy()
    paths = [str(PACKAGES / n / '.lake/build/lib/lean') for n in state['package_revisions']]
    if any((Path(p) / 'Openmath').exists() for p in paths):
        raise RuntimeError('external package shadows Openmath')
    env['LEAN_PATH'] = ':'.join([str(BUILD), *paths])
    env['OURS'] = ','.join(state['order'])
    return env


def verify_state(state):
    if state['target'] != TARGET or state['chunk_size'] != CHUNK or state['kernel_chunk_size'] != KERNEL_CHUNK:
        raise RuntimeError('state target or chunk size changed')
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
        raise RuntimeError('Lean toolchain changed')
    for rel, expected in state['input_hashes'].items():
        if sha(ROOT / rel) != expected or sha(BUILD / rel) != expected:
            raise RuntimeError(f'input changed during phased check: {rel}')
    if current_sources() != state['source_hashes']:
        raise RuntimeError('source manifest payload changed during phased check')
    for module in state['order']:
        rel = Path(*module.split('.')).with_suffix('.lean')
        if sha(BUILD / '.sources' / rel) != state['source_hashes'][str(rel)]:
            raise RuntimeError(f'frozen source changed: {rel}')
    if closure(TARGET, state['source_hashes']) != state['order']:
        raise RuntimeError('import closure changed')
    for name, expected in state['package_revisions'].items():
        actual, dirty = git_state(name)
        if actual != expected or dirty:
            raise RuntimeError(f'package revision or tracked file changed: {name}')
    if sha(LEAN) != state['lean_sha256'] or sha(LEANCHECKER) != state['leanchecker_sha256']:
        raise RuntimeError('Lean binary changed')
    for module, record in state['builds'].items():
        rel = Path(*module.split('.')).with_suffix('.olean')
        if sha(BUILD / rel) != record['olean_sha256']:
            raise RuntimeError(f'built olean changed: {module}')
        if sha(RECEIPTS / record['log']) != record['log_sha256']:
            raise RuntimeError(f'build log changed: {module}')
    for record in state['replays'].values():
        if sha(RECEIPTS / record['log']) != record['log_sha256']:
            raise RuntimeError(f'kernel replay log changed: {record["log"]}')


def prepare():
    SUCCESS.unlink(missing_ok=True)
    STATE.unlink(missing_ok=True)
    if BUILD.exists():
        shutil.rmtree(BUILD)
    BUILD.mkdir()
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
        raise RuntimeError('unexpected Lean toolchain')
    inputs = {rel: sha(ROOT / rel) for rel in INPUTS}
    for rel, expected in inputs.items():
        dst = BUILD / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, dst)
        if sha(dst) != expected:
            raise RuntimeError(f'input changed during snapshot: {rel}')
    pinned = current_sources()
    order = closure(TARGET, pinned)
    if {m.replace('.', '/') + '.lean' for m in order} != set(pinned):
        raise RuntimeError('packaged sources outside expanded target closure')
    if set(SCOPE['module_lean_flags']) - set(order):
        raise RuntimeError('resource profile references a module outside closure')
    if set(AXIOM_MODULES.values()) - set(order):
        raise RuntimeError('declaration ownership references a module outside closure')
    data = package_manifest()
    revs = {}
    for p in data['packages']:
        actual, dirty = git_state(p['name'])
        if actual != p['rev'] or dirty:
            raise RuntimeError(f'package mismatch or dirty tracked files: {p["name"]}')
        revs[p['name']] = actual
    state = {
        'target': TARGET, 'chunk_size': CHUNK, 'kernel_chunk_size': KERNEL_CHUNK,
        'input_hashes': inputs,
        'source_hashes': pinned, 'order': order, 'package_revisions': revs,
        'lean_sha256': sha(LEAN), 'leanchecker_sha256': sha(LEANCHECKER),
        'builds': {}, 'next_chunk': 0, 'replays': {}, 'next_kernel_chunk': 0,
    }
    env = environment(state)
    for script, pin, log in [
        ('toolchain_pins.py', 'toolchain.sha256', 'final-toolchain-pins-pre.log'),
        ('olean_pins.py', 'package-oleans.sha256', 'final-package-olean-pins-pre.log'),
    ]:
        root = LEAN.parent.parent if script.startswith('toolchain') else PACKAGES
        checked_run([sys.executable, '-I', str(BUILD / 'tools' / script),
                     'verify', str(root), str(BUILD / 'pins' / pin)],
                    env, RECEIPTS / log)
        state[log] = sha(RECEIPTS / log)
    sources = []
    for module in order:
        rel = Path(*module.split('.')).with_suffix('.lean')
        dst = BUILD / '.sources' / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, dst)
        if sha(dst) != pinned[str(rel)]:
            raise RuntimeError(f'source changed during snapshot: {rel}')
        sources.append(dst)
    checked_run([sys.executable, '-I', str(BUILD / 'tools/srcscan.py'), *map(str, sources)],
                env, RECEIPTS / 'final-source-scan.log')
    state['source_scan_sha256'] = sha(RECEIPTS / 'final-source-scan.log')
    verify_state(state)
    write_json(STATE, state)
    print(json.dumps({'phase': 'prepare', 'modules': len(order),
                      'chunks': (len(order) + CHUNK - 1) // CHUNK,
                      'state_sha256': sha(STATE)}))


def build(index):
    state = json.loads(STATE.read_text())
    verify_state(state)
    if index != state['next_chunk']:
        raise RuntimeError(f'expected build chunk {state["next_chunk"]}, got {index}')
    start = index * CHUNK
    end = min(start + CHUNK, len(state['order']))
    if start >= end:
        raise RuntimeError('build chunk index out of range')
    env = environment(state)
    for module in state['order'][start:end]:
        rel = Path(*module.split('.')).with_suffix('.lean')
        source = BUILD / '.sources' / rel
        output = BUILD / rel.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = f'final-{module.rsplit(".", 1)[-1]}.build.log'
        result = checked_run([str(LEAN), '-Ddebug.skipKernelTC=false',
                              '-DmaxHeartbeats=2000000', *SCOPE['module_lean_flags'].get(module, []), '-o', str(output), str(source)],
                             env, RECEIPTS / log)
        if module in {TARGET, 'Openmath.Erdos643R3.CoefficientOneFinal'} and 'warning:' in result.stdout + result.stderr:
            raise RuntimeError(f'compile warning: {module}; see {log}')
        state['builds'][module] = {
            'source_sha256': sha(source), 'olean_sha256': sha(output),
            'log': log, 'log_sha256': sha(RECEIPTS / log),
        }
        write_json(STATE, state)
    state['next_chunk'] += 1
    verify_state(state)
    write_json(STATE, state)
    print(json.dumps({'phase': 'build', 'chunk': index, 'built': len(state['builds']),
                      'remaining': len(state['order']) - len(state['builds']),
                      'state_sha256': sha(STATE)}))


def hygiene():
    state = json.loads(STATE.read_text())
    verify_state(state)
    if len(state['builds']) != len(state['order']):
        raise RuntimeError('not all imports built')
    env = environment(state)
    log = RECEIPTS / 'final.hygiene.log'
    checked_run([str(LEAN), '--run', str(BUILD / 'tools/Hygiene.lean'), TARGET,
                 *AXIOM_THEOREMS], env, log)
    output = log.read_text()
    if 'HYGIENE ok' not in output:
        raise RuntimeError('hygiene did not report ok')
    for name in AXIOM_THEOREMS:
        module = AXIOM_MODULES.get(name, f'Openmath.{name.rsplit(".", 1)[0]}')
        line = f'DECL {name} module={module} '
        if line not in output:
            raise RuntimeError(f'defining module mismatch: {name}')
    state['hygiene_sha256'] = sha(log)
    verify_state(state)
    write_json(STATE, state)
    print(json.dumps({'phase': 'hygiene', 'declarations': len(AXIOM_THEOREMS),
                      'state_sha256': sha(STATE)}))


def kernel(index):
    state = json.loads(STATE.read_text())
    verify_state(state)
    if 'hygiene_sha256' not in state or sha(RECEIPTS / 'final.hygiene.log') != state['hygiene_sha256']:
        raise RuntimeError('hygiene phase missing or changed')
    if index != state['next_kernel_chunk']:
        raise RuntimeError(f'expected kernel chunk {state["next_kernel_chunk"]}, got {index}')
    start = index * KERNEL_CHUNK
    end = min(start + KERNEL_CHUNK, len(state['order']))
    if start >= end:
        raise RuntimeError('kernel chunk index out of range')
    env = environment(state)
    log_name = f'final.kernel.{index}.log'
    log = RECEIPTS / log_name
    checked_run([str(LEANCHECKER), *state['order'][start:end]], env, log)
    state['replays'][str(index)] = {'modules': state['order'][start:end],
                                    'log': log_name, 'log_sha256': sha(log)}
    state['next_kernel_chunk'] += 1
    verify_state(state)
    write_json(STATE, state)
    print(json.dumps({'phase': 'kernel', 'chunk': index,
                      'modules': len(state['order'][start:end]),
                      'state_sha256': sha(STATE)}))


def finalize():
    state = json.loads(STATE.read_text())
    verify_state(state)
    if 'hygiene_sha256' not in state or sha(RECEIPTS / 'final.hygiene.log') != state['hygiene_sha256']:
        raise RuntimeError('hygiene phase missing or changed')
    if state['next_kernel_chunk'] != (len(state['order']) + KERNEL_CHUNK - 1) // KERNEL_CHUNK:
        raise RuntimeError('kernel replay coverage incomplete')
    replayed = [m for i in range(state['next_kernel_chunk'])
                for m in state['replays'][str(i)]['modules']]
    if replayed != state['order']:
        raise RuntimeError('kernel replay order/coverage differs from import closure')
    env = environment(state)
    probe_text = f'import {TARGET}\n' + ''.join(f'#print axioms {name}\n' for name in AXIOM_THEOREMS)
    probe_log = RECEIPTS / 'final.axioms.log'
    probe = checked_run([str(LEAN), '-Ddebug.skipKernelTC=false',
                         '-DmaxHeartbeats=2000000', '--stdin'], env, probe_log, probe_text)
    output = probe.stdout + probe.stderr
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    checks = {}
    for name in AXIOM_THEOREMS:
        pattern = r"'" + re.escape(name) + r"' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
        match = re.search(pattern, output)
        if not match:
            raise RuntimeError(f'axiom output missing: {name}')
        axioms = [] if match.group(1) is None else [a.strip() for a in match.group(1).split(',')]
        if not set(axioms) <= allowed:
            raise RuntimeError(f'disallowed axioms: {name} {axioms}')
        checks[name] = axioms
    for script, pin, log in [
        ('toolchain_pins.py', 'toolchain.sha256', 'final-toolchain-pins-post.log'),
        ('olean_pins.py', 'package-oleans.sha256', 'final-package-olean-pins-post.log'),
    ]:
        root = LEAN.parent.parent if script.startswith('toolchain') else PACKAGES
        checked_run([sys.executable, '-I', str(BUILD / 'tools' / script),
                     'verify', str(root), str(BUILD / 'pins' / pin)],
                    env, RECEIPTS / log)
        state[log] = sha(RECEIPTS / log)
    verify_state(state)
    receipt = {
        'result': 'PASS_FULL_COEFFICIENT_ONE_AND_DESIGN',
        'full_design_existence_verified': True,
        'full_coefficient_one_verified': True,
        'checker': 'isolated-phased-check.sh',
        'timestamp_utc': datetime.now(timezone.utc).isoformat(),
        'state_sha256': sha(STATE), 'target': TARGET,
        'source_hashes': state['source_hashes'], 'input_hashes': state['input_hashes'],
        'order': state['order'], 'package_revisions': state['package_revisions'],
        'lean_sha256': state['lean_sha256'], 'leanchecker_sha256': state['leanchecker_sha256'],
        'builds': state['builds'], 'kernel_replays': state['replays'], 'axioms': checks,
        'source_scan_sha256': state['source_scan_sha256'],
        'hygiene_sha256': state['hygiene_sha256'],
        'axiom_log_sha256': sha(probe_log),
        'toolchain_pin_pre_sha256': state['final-toolchain-pins-pre.log'],
        'package_pin_pre_sha256': state['final-package-olean-pins-pre.log'],
        'toolchain_pin_post_sha256': state['final-toolchain-pins-post.log'],
        'package_pin_post_sha256': state['final-package-olean-pins-post.log'],
        'unproved_inputs': [],
        'limitations': SCOPE['limitations'],
    }
    write_json(SUCCESS, receipt)
    FAILURE.unlink(missing_ok=True)
    print(f'RESULT: PASS sha256={sha(SUCCESS)} modules={len(state["order"])} declarations={len(checks)}')


def main():
    global LEAN, LEANCHECKER, PACKAGES
    arg = sys.argv[1] if len(sys.argv) > 1 else ''
    RECEIPTS.mkdir(exist_ok=True)
    # Validate sources before runtime discovery so missing sources fail independently.
    current_sources()
    LEAN, LEANCHECKER, PACKAGES = discover(ROOT)
    if arg == '--final-prepare' and len(sys.argv) == 2:
        prepare()
    elif arg.startswith('--final-build-') and len(sys.argv) == 2:
        build(int(arg.rsplit('-', 1)[1]))
    elif arg == '--final-hygiene' and len(sys.argv) == 2:
        hygiene()
    elif arg.startswith('--final-kernel-') and len(sys.argv) == 2:
        kernel(int(arg.rsplit('-', 1)[1]))
    elif arg == '--final-finalize' and len(sys.argv) == 2:
        finalize()
    else:
        raise RuntimeError('usage: check.sh prepare|build N|hygiene|kernel N|finalize')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        SUCCESS.unlink(missing_ok=True)
        result = 'UNKNOWN' if 'UNKNOWN timeout' in str(exc) else 'FAIL'
        write_json(FAILURE, {
            'result': result,
            'phase': sys.argv[1:] if len(sys.argv) > 1 else [],
            'timestamp_utc': datetime.now(timezone.utc).isoformat(),
            'error': str(exc),
        })
        print(f'RESULT: {result} {exc}', file=sys.stderr)
        sys.exit(1)
