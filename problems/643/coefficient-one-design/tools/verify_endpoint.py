#!/usr/bin/env python3
"""Fresh local-import build and axiom probe for the coefficient-one endpoint interface."""

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

from srcscan import strip
from runtime import discover


ROOT = Path(__file__).resolve().parents[1]
LEAN = LEANCHECKER = PACKAGES = None
BUILD = ROOT / '.verified-build'
RECEIPTS = ROOT / 'receipts'
UPSTREAM = len(sys.argv) > 1 and sys.argv[1] == '--upstream'
M7 = len(sys.argv) > 1 and sys.argv[1] == '--m7'
FINAL = len(sys.argv) > 1 and sys.argv[1].startswith('--final')
if __name__ == '__main__' and (len(sys.argv) > 2 or (len(sys.argv) > 1 and not (UPSTREAM or M7 or FINAL))):
    raise SystemExit('usage: verify_endpoint.py [--upstream|--m7|--final]')
TARGET = ('Openmath.Erdos643R3.PublicSmallOrders' if FINAL else
          'Openmath.Erdos643R3.CoefficientOneUpstream' if UPSTREAM else
          'Openmath.Erdos643R3.CoefficientOneAssembly' if M7 else
          'Openmath.Erdos643R3.CoefficientOne')
LABEL = 'final' if FINAL else 'upstream' if UPSTREAM else 'm7' if M7 else 'endpoint'
AXIOM_THEOREMS = [
    'Erdos643R3.CoefficientOne.uniform_iff_basics',
    'Erdos643R3.CoefficientOne.literal_avoidance_iff_not_forbidden',
    'Erdos643R3.CoefficientOne.card_le_choose_three',
    'Erdos643R3.CoefficientOne.coefficient_one_small_hosts',
    'Erdos643R3.CoefficientOne.coefficient_one_of_phi_nonpos',
    'Erdos643R3.CoefficientOne.phi_nonpos_of_recovery',
    'Erdos643R3.CoefficientOne.coefficient_one_of_recovery',
]
if UPSTREAM:
    AXIOM_THEOREMS += [
        'Erdos643R3.CoefficientOneUpstream.repeated_iff_forbidden',
        'Erdos643R3.CoefficientOneUpstream.uniform_three_iff',
        'Erdos643R3.CoefficientOneUpstream.extremal_three_le_choose_two',
        'Erdos643R3.CoefficientOneUpstream.forcing_three_le_choose_two_add_one',
    ]
if M7:
    AXIOM_THEOREMS = [
        'Erdos643R3.G1Main.theoremG1',
        'Erdos643R3.BothLight.bicone_both_light',
        'Erdos643R3.Redistribution.hrec_of_funded_bicones',
        'Erdos643R3.CPrime.funded_of_G1_G3hPrime',
        'Erdos643R3.CPrimeMain.funded_of_G3hPrime',
        'Erdos643R3.CPrimeMain.recovery_of_G3hPrime',
        'Erdos643R3.CPrimeMain.endpoint_of_G3hPrime',
        'Erdos643R3.CoefficientOneAssembly.recovery_of_G3hPrimeAt',
        'Erdos643R3.CoefficientOneAssembly.coefficient_one_of_G3hPrimeAt',
    ]
if FINAL:
    AXIOM_THEOREMS = [
        'Erdos643R3.AnchorComplete.g3hPrime',
        'Erdos643R3.CoefficientOneAssembly.coefficient_one_of_G3hPrimeAt',
        'Erdos643R3.CoefficientOneFinal.coefficient_one',
        'Erdos643R3.CoefficientOneFinal.phi_nonpos',
        'Erdos643R3.CoefficientOneFinal.shadow_colink_bound',
        'Erdos643R3.CoefficientOneFinal.extremal_three_le_choose_two',
        'Erdos643R3.CoefficientOneFinal.forcing_three_le_choose_two_add_one',
        'Erdos643R3.CoefficientOneFinal.extremal_three_bounds',
        'Erdos643R3.CoefficientOneFinal.extremal_three_lower_matching',
        'Erdos643R3.CoefficientOneFinal.extremal_eq_of_supplied_design',
        'Erdos643R3.CoefficientOneFinal.extremal_ratio_tendsto_one',
        'Erdos643R3.CoefficientOneFinal.forcing_isEquivalent',
        'Erdos643Design.design_one',
        'Erdos643Design.design_five',
        'Erdos643R3.PublicSmallOrders.extremal_one',
        'Erdos643R3.PublicSmallOrders.extremal_five',
    ]

AXIOM_MODULES = {
    'Erdos643Design.design_one': 'Openmath.Erdos643R3.DesignBaseOrders',
    'Erdos643Design.design_five': 'Openmath.Erdos643R3.DesignBaseOrders',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(target, pinned):
    order = []
    active = set()
    done = set()

    def visit(module):
        if module in done:
            return
        if module in active:
            raise RuntimeError(f'cyclic local import: {module}')
        rel = Path(*module.split('.')).with_suffix('.lean')
        if str(rel) not in pinned:
            raise RuntimeError(f'unpinned local import: {module}')
        source = ROOT / rel
        if sha(source) != pinned[str(rel)]:
            raise RuntimeError(f'source changed: {rel}')
        active.add(module)
        code = strip(source.read_text())
        for imports in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)$', code, re.M):
            for dep in imports.split():
                if dep.startswith(('Openmath.', 'FormalConjecturesForMathlib.')):
                    visit(dep)
        active.remove(module)
        done.add(module)
        order.append(module)

    visit(target)
    return order


def checked_run(cmd, env, log, stdin=None):
    try:
        result = subprocess.run(cmd, env=env, input=stdin, capture_output=True,
                                text=True, timeout=240)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f'UNKNOWN timeout 240s: {cmd[0]} {cmd[1:3]}') from exc
    log.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'command failed (exit {result.returncode}): {cmd}; see {log}')
    return result


def main():
    global LEAN, LEANCHECKER, PACKAGES
    LEAN, LEANCHECKER, PACKAGES = discover(ROOT)
    frozen_inputs = [
        'check.sh', 'tools/test_failure_control.py',
        'tools/verify_endpoint.py', 'tools/Hygiene.lean', 'tools/srcscan.py',
        'tools/olean_pins.py', 'tools/toolchain_pins.py', 'tools/runtime.py',
        'source-manifest.json', 'new-source-manifest.json',
        'upstream-source-manifest.json', 'LICENSE.upstream',
        'lake-manifest.json', 'standalone/lake-manifest.json',
        'lakefile.toml', 'lean-toolchain',
        'pins/package-oleans.sha256', 'pins/toolchain.sha256',
    ]
    input_hashes = {rel: sha(ROOT / rel) for rel in frozen_inputs}
    if BUILD.exists():
        shutil.rmtree(BUILD)
    BUILD.mkdir()
    frozen_tools = BUILD / 'tools'
    for rel in frozen_inputs:
        dst = BUILD / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, dst)
        if sha(dst) != input_hashes[rel]:
            raise RuntimeError(f'input changed during snapshot: {rel}')
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    new_manifest = json.loads((ROOT / 'new-source-manifest.json').read_text())
    if set(manifest) & set(new_manifest):
        raise RuntimeError('new and canonical manifests overlap')
    pinned = manifest | new_manifest
    if UPSTREAM or FINAL:
        upstream_manifest = json.loads((ROOT / 'upstream-source-manifest.json').read_text())
        if sha(ROOT / 'LICENSE.upstream') != upstream_manifest['license_sha256']:
            raise RuntimeError('upstream license changed')
        pinned |= upstream_manifest['files']
    for rel, expected in pinned.items():
        if sha(ROOT / rel) != expected:
            raise RuntimeError(f'source changed: {rel}')
    order = closure(TARGET, pinned)
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
        raise RuntimeError('toolchain pin changed')
    package_manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    if (ROOT / 'lake-manifest.json').read_bytes() != (ROOT / 'standalone/lake-manifest.json').read_bytes():
        raise RuntimeError('root and standalone package manifests differ')
    lakefile = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    requires = [p for p in lakefile['require'] if p['name'] == 'mathlib']
    if len(requires) != 1 or requires[0]['rev'] != next(
        p['rev'] for p in package_manifest['packages'] if p['name'] == 'mathlib'
    ):
        raise RuntimeError('lakefile Mathlib pin differs from lake-manifest')
    package_revs = {}
    for package in package_manifest['packages']:
        name, expected = package['name'], package['rev']
        try:
            actual = subprocess.run(
                ['git', '-C', str(PACKAGES / name), 'rev-parse', 'HEAD'],
                check=True, capture_output=True, text=True, timeout=240,
            ).stdout.strip()
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(f'UNKNOWN timeout 240s: git revision {name}') from exc
        if actual != expected:
            raise RuntimeError(f'package pin changed: {name} expected={expected} actual={actual}')
        try:
            dirty = subprocess.run(['git', '-C', str(PACKAGES / name), 'status', '--porcelain',
                                    '--untracked-files=no'], check=True, capture_output=True,
                                   text=True, timeout=240).stdout.strip()
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(f'UNKNOWN timeout 240s: git status {name}') from exc
        if dirty:
            raise RuntimeError(f'package tracked files dirty: {name}')
        package_revs[name] = actual
    mathlib = package_revs['mathlib']
    package_paths = [str(PACKAGES / name / '.lake/build/lib/lean') for name in package_revs]
    if not package_paths:
        raise RuntimeError('package build paths missing')
    if any((Path(p) / 'Openmath').exists() for p in package_paths):
        raise RuntimeError('external package shadows Openmath')
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(BUILD), *package_paths])
    lean_sha_start, leanchecker_sha_start = sha(LEAN), sha(LEANCHECKER)
    RECEIPTS.mkdir(exist_ok=True)
    toolchain_log = RECEIPTS / 'toolchain-pins.log'
    checked_run([sys.executable, '-I', str(frozen_tools / 'toolchain_pins.py'),
                 'verify', str(LEAN.parent.parent), str(BUILD / 'pins/toolchain.sha256')],
                env, toolchain_log)
    packages_log = RECEIPTS / 'package-olean-pins.log'
    checked_run([sys.executable, '-I', str(frozen_tools / 'olean_pins.py'),
                 'verify', str(PACKAGES), str(BUILD / 'pins/package-oleans.sha256')],
                env, packages_log)
    frozen = BUILD / '.sources'
    sources = []
    for module in order:
        rel = Path(*module.split('.')).with_suffix('.lean')
        dst = frozen / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, dst)
        if sha(dst) != pinned[str(rel)]:
            raise RuntimeError(f'copy changed during snapshot: {rel}')
        sources.append(dst)
    scan_log = RECEIPTS / f'{LABEL}-source-scan.log'
    checked_run([sys.executable, '-I', str(frozen_tools / 'srcscan.py'),
                 *map(str, sources)], env, scan_log)
    modules = []
    for module in order:
        rel = Path(*module.split('.')).with_suffix('.lean')
        src = frozen / rel
        out = BUILD / rel.with_suffix('.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(LEAN), '-Ddebug.skipKernelTC=false', '-DmaxHeartbeats=2000000',
               '-o', str(out), str(src)]
        log = RECEIPTS / f'{module.rsplit(".",1)[-1]}.build.log'
        result = checked_run(cmd, env, log)
        modules.append({'module': module, 'source_sha256': sha(src),
                        'exit': result.returncode, 'log_sha256': sha(log)})
        if module in {TARGET, 'Openmath.Erdos643R3.CoefficientOneFinal'} and 'warning:' in result.stdout + result.stderr:
            raise RuntimeError(f'compile warned: {module}; see {log}')
    env['OURS'] = ','.join(order)
    hygiene_log = RECEIPTS / f'{LABEL}.hygiene.log'
    checked_run([str(LEAN), '--run', str(frozen_tools / 'Hygiene.lean'), TARGET,
                 *AXIOM_THEOREMS], env, hygiene_log)
    if 'HYGIENE ok' not in hygiene_log.read_text():
        raise RuntimeError('hygiene did not report ok')
    for name in AXIOM_THEOREMS:
        defining_module = AXIOM_MODULES.get(name, 'Openmath.' + name.rsplit('.', 1)[0])
        line = f'DECL {name} module={defining_module} '
        if line not in hygiene_log.read_text():
            raise RuntimeError(f'declaration not defined in expected source module: {name}')
    replay_log = RECEIPTS / f'{LABEL}.replay.log'
    checked_run([str(LEANCHECKER), *order], env, replay_log)
    probe_text = f'import {TARGET}\n' + ''.join(
        f'#print axioms {name}\n' for name in AXIOM_THEOREMS
    )
    probe_log = RECEIPTS / f'{LABEL}.axioms.log'
    probe = checked_run([str(LEAN), '-Ddebug.skipKernelTC=false',
                         '-DmaxHeartbeats=2000000', '--stdin'],
                        env, probe_log, probe_text)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    output = probe.stdout + probe.stderr
    checks = {}
    for name in AXIOM_THEOREMS:
        pattern = r"'" + re.escape(name) + r"' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
        match = re.search(pattern, output)
        if not match:
            raise RuntimeError(f'axiom output missing or malformed for {name}: {probe_log}')
        axioms = [] if match.group(1) is None else [a.strip() for a in match.group(1).split(',')]
        if not set(axioms) <= allowed:
            raise RuntimeError(f'disallowed axioms for {name}: {axioms}')
        checks[name] = axioms
    post_toolchain_log = RECEIPTS / f'{LABEL}-toolchain-pins-post.log'
    checked_run([sys.executable, '-I', str(frozen_tools / 'toolchain_pins.py'),
                 'verify', str(LEAN.parent.parent), str(BUILD / 'pins/toolchain.sha256')],
                env, post_toolchain_log)
    post_packages_log = RECEIPTS / f'{LABEL}-package-olean-pins-post.log'
    checked_run([sys.executable, '-I', str(frozen_tools / 'olean_pins.py'),
                 'verify', str(PACKAGES), str(BUILD / 'pins/package-oleans.sha256')],
                env, post_packages_log)
    if sha(LEAN) != lean_sha_start or sha(LEANCHECKER) != leanchecker_sha_start:
        raise RuntimeError('Lean or leanchecker changed during run')
    for name, expected in package_revs.items():
        try:
            actual = subprocess.run(['git', '-C', str(PACKAGES / name), 'rev-parse', 'HEAD'],
                                    check=True, capture_output=True, text=True, timeout=240).stdout.strip()
            dirty = subprocess.run(['git', '-C', str(PACKAGES / name), 'status', '--porcelain',
                                    '--untracked-files=no'], check=True, capture_output=True,
                                   text=True, timeout=240).stdout.strip()
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(f'UNKNOWN timeout 240s: post-build git check {name}') from exc
        if actual != expected or dirty:
            raise RuntimeError(f'package changed during run: {name}')
    for rel, expected in input_hashes.items():
        if sha(ROOT / rel) != expected or sha(BUILD / rel) != expected:
            raise RuntimeError(f'input changed during run: {rel}')
    for rel, expected in pinned.items():
        if sha(ROOT / rel) != expected:
            raise RuntimeError(f'source changed during run: {rel}')
    for path in sources:
        rel = str(path.relative_to(frozen))
        if sha(path) != pinned[rel]:
            raise RuntimeError(f'frozen source changed during run: {rel}')
    receipt = {
        'result': ('PASS_FULL_COEFFICIENT_ONE' if FINAL else
                   'PASS_CONDITIONAL_UPSTREAM_BRIDGE_ONLY' if UPSTREAM else
                   'PASS_M7_CONDITIONAL_G3H_ONLY' if M7 else
                   'PASS_CONDITIONAL_INTERFACE_ONLY'),
        'timestamp_utc': datetime.now(timezone.utc).isoformat(),
        'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'lean_binary_sha256': sha(LEAN),
        'leanchecker_binary_sha256': sha(LEANCHECKER),
        'mathlib_revision': mathlib,
        'package_revisions': package_revs,
        'canonical20_manifest_sha256': sha(ROOT / 'source-manifest.json'),
        'frozen_inputs': input_hashes,
        'new_source_manifest_sha256': sha(ROOT / 'new-source-manifest.json'),
        'upstream_source_manifest_sha256': (sha(ROOT / 'upstream-source-manifest.json')
                                            if UPSTREAM or FINAL else None),
        'srcscan_sha256': sha(ROOT / 'tools/srcscan.py'),
        'hygiene_checker_sha256': sha(ROOT / 'tools/Hygiene.lean'),
        'verifier_sha256': sha(ROOT / 'tools/verify_endpoint.py'),
        'toolchain_pin_manifest_sha256': sha(ROOT / 'pins/toolchain.sha256'),
        'package_olean_pin_manifest_sha256': sha(ROOT / 'pins/package-oleans.sha256'),
        'toolchain_pin_log_sha256': sha(toolchain_log),
        'post_toolchain_pin_log_sha256': sha(post_toolchain_log),
        'package_olean_pin_log_sha256': sha(packages_log),
        'post_package_olean_pin_log_sha256': sha(post_packages_log),
        'source_scan_log_sha256': sha(scan_log),
        'hygiene_log_sha256': sha(hygiene_log),
        'replay_log_sha256': sha(replay_log),
        'modules': modules,
        'axioms': checks,
        'axiom_log_sha256': sha(probe_log),
        'unproved_inputs': ([] if FINAL else
                            ['CoefficientOneAt (Fin n)', 'RecoveryAt V', 'PhiNonposAt V']
                            if UPSTREAM else ['CPrime.G3hPrime H'] if M7 else
                            ['RecoveryAt V', 'PhiNonposAt V']),
        'full_coefficient_one_verified': FINAL,
    }
    (RECEIPTS / f'{LABEL}-receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'result': receipt['result'], 'modules': len(modules),
                      'declarations': len(checks),
                      'receipt_sha256': sha(RECEIPTS / f'{LABEL}-receipt.json')}))


if __name__ == '__main__':
    success_receipt = RECEIPTS / f'{LABEL}-receipt.json'
    if success_receipt.exists():
        success_receipt.unlink()
    try:
        main()
    except Exception as exc:
        RECEIPTS.mkdir(exist_ok=True)
        (RECEIPTS / f'{LABEL}-failure.json').write_text(json.dumps({
            'timestamp_utc': datetime.now(timezone.utc).isoformat(),
            'result': 'UNKNOWN' if 'UNKNOWN timeout' in str(exc) else 'FAIL',
            'error': str(exc),
        }, indent=2, sort_keys=True) + '\n')
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
    else:
        (RECEIPTS / f'{LABEL}-failure.json').unlink(missing_ok=True)
