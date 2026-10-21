#!/usr/bin/env python3
"""Self-contained negative controls; no proof build or existing receipt required."""
import importlib
import itertools
import json
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
results = {}
with tempfile.TemporaryDirectory(prefix='erdos643-controls-') as td:
    work = Path(td)
    for fault in ('source', 'timeout'):
        copy = work / fault
        shutil.copytree(ROOT, copy, ignore=shutil.ignore_patterns(
            '.lake', '.verified-*', 'receipts', '__pycache__', 'fixtures'))
        receipts = copy / 'receipts'
        receipts.mkdir()
        (receipts / 'final-receipt.json').write_text('{"synthetic_control": true}\n')
        if fault == 'source':
            (copy / 'Openmath/Erdos643R3/CoefficientOneFinal.lean').write_text('-- changed\n')
            command = ['sh', str(copy / 'check.sh'), 'prepare']
        else:
            bootstrap = (
                'import sys,runpy;sys.path.insert(0,"tools");import runtime;'
                'runtime.discover=lambda root: (_ for _ in ()).throw('
                'RuntimeError("UNKNOWN timeout 240s: injected runtime control"));'
                'sys.argv=["tools/verify_final_phased.py","--final-prepare"];'
                'runpy.run_path("tools/verify_final_phased.py",run_name="__main__")')
            command = [sys.executable, '-B', '-c', bootstrap]
        run = subprocess.run(command, cwd=copy, capture_output=True, text=True, timeout=240)
        failure = json.loads((receipts / 'final-failure.json').read_text())
        expected = 'FAIL' if fault == 'source' else 'UNKNOWN'
        assert run.returncode != 0 and failure['result'] == expected
        assert not (receipts / 'final-receipt.json').exists()
        results[fault + '_invalidates_stale_success'] = expected
    sys.path.insert(0, str(ROOT / 'tools'))
    old_args = sys.argv
    sys.argv = ['control', '--final-prepare']
    verifier = importlib.import_module('verify_final_phased')
    sys.argv = old_args
    statepath = work / 'state.json'
    state = {'next_chunk': 0, 'builds': {}, 'order': ['Openmath.Fixture'], 'next_kernel_chunk': 0}
    statepath.write_text(json.dumps(state))
    with patch.object(verifier, 'STATE', statepath), patch.object(verifier, 'verify_state', lambda s: None):
        for name, call, message in [
            ('out_of_order_build', lambda: verifier.build(1), 'expected build chunk'),
            ('incomplete_build_hygiene', verifier.hygiene, 'not all imports built'),
            ('kernel_without_hygiene', lambda: verifier.kernel(0), 'hygiene phase missing'),
            ('finalize_without_hygiene', verifier.finalize, 'hygiene phase missing')]:
            try:
                call()
            except RuntimeError as exc:
                assert message in str(exc), (name, exc)
                results[name] = 'REJECTED'
            else:
                raise AssertionError(name)
    with patch.object(verifier.subprocess, 'run', side_effect=subprocess.TimeoutExpired('fixture', 240)):
        try:
            verifier.checked_run(['fixture'], {}, work / 'timeout.log')
        except RuntimeError as exc:
            assert 'UNKNOWN timeout 240s' in str(exc)
            results['subprocess_timeout_classification'] = 'UNKNOWN'
        else:
            raise AssertionError('timeout accepted')
    from srcscan import scan
    forbidden = work / 'forbidden.lean'
    forbidden.write_text('theorem rejected : True := by native_decide\n')
    assert 'native_decide' in scan(forbidden)[0]
    results['native_decide_scan'] = 'REJECTED'
    results['pinned_source_closure'] = len(verifier.closure(verifier.TARGET, verifier.current_sources()))
    import runtime
    with patch.dict(runtime.os.environ, {}, clear=True), \
         patch.object(runtime.shutil, 'which', return_value='fixture-lean'), \
         patch.object(runtime.subprocess, 'run', side_effect=[
             subprocess.CompletedProcess([], 0, str(work / 'toolchain') + '\n', ''),
             subprocess.CompletedProcess([], 0, 'Lean (version 4.33.1, fixture)\n', '')]):
        prefix = (work / 'toolchain').resolve()
        (prefix / 'bin').mkdir(parents=True)
        for name in ('lean', 'leanchecker'): (prefix / 'bin' / name).write_bytes(b'fixture')
        lean, checker, packages = runtime.discover(ROOT)
        assert lean == prefix / 'bin/lean' and checker == prefix / 'bin/leanchecker'
        assert packages == ROOT / '.lake/packages'
        results['default_runtime_locations'] = 'PACKAGE_LOCAL_DEPENDENCIES'
    with patch.dict(runtime.os.environ, {'ERDOS643_TOOLCHAIN': str(prefix)}, clear=True), \
         patch.object(runtime.subprocess, 'run', return_value=subprocess.CompletedProcess(
             [], 0, 'Lean (version 0.0.0, fixture)\n', '')):
        try: runtime.discover(ROOT)
        except RuntimeError as exc:
            assert 'version differs' in str(exc)
            results['wrong_lean_version'] = 'REJECTED'
        else: raise AssertionError('wrong version accepted')
    for helper, rel in [('toolchain_pins.py', 'bin/lean'),
                        ('olean_pins.py', 'mathlib/.lake/build/lib/lean/Fixture.olean')]:
        fixture = work / helper
        target = fixture / rel
        target.parent.mkdir(parents=True)
        target.write_bytes(b'fixture binary')
        pins = work / (helper + '.pins')
        script = ROOT / 'tools' / helper
        run = subprocess.run([sys.executable, '-I', str(script), 'make', str(fixture), str(pins)],
                             capture_output=True, text=True, timeout=240)
        assert run.returncode == 0
        for mutation in ('changed', 'missing', 'extra'):
            target.write_bytes(b'fixture binary')
            extra = target.with_name('extra' + target.suffix)
            extra.unlink(missing_ok=True)
            if mutation == 'changed': target.write_bytes(b'changed')
            elif mutation == 'missing': target.unlink()
            else: extra.write_bytes(b'extra')
            run = subprocess.run([sys.executable, '-I', str(script), 'verify', str(fixture), str(pins)],
                                 capture_output=True, text=True, timeout=240)
            assert run.returncode != 0, (helper, mutation)
            results[helper + '_' + mutation] = 'REJECTED'
    for wrapper, case in itertools.product(('run_phase', 'setup'), ('timeout', 'ordinary_failure', 'success')):
        copy = work / ('descendant-' + wrapper + '-' + case)
        (copy / 'tools').mkdir(parents=True)
        (copy / 'bin').mkdir()
        (copy / 'receipts').mkdir()
        for name in (wrapper + '.py', 'bounded_process.py'):
            shutil.copyfile(ROOT / 'tools' / name, copy / 'tools' / name)
        (copy / 'receipts/final-receipt.json').write_text('{"synthetic_control":true}\n')
        # The child acknowledges startup, then waits until the wrapper has
        # exited before it is permitted to write. A surviving descendant
        # therefore cannot pass just because its scheduled write was delayed.
        (copy / 'child.py').write_text(
            'from pathlib import Path\nimport time\n'
            'Path("child-ready").write_text("ready")\n'
            'while not Path("permit-write").exists(): time.sleep(0.01)\n'
            'Path("child-marker").write_text("survived")\n')
        ending = 'time.sleep(60)\n' if case == 'timeout' else (
            'from pathlib import Path\n'
            'while not Path("child-ready").exists(): time.sleep(0.01)\n'
            'sys.exit(' + ('7' if case == 'ordinary_failure' else '0') + ')\n')
        (copy / 'launcher.py').write_text(
            'import subprocess,sys,time\n'
            'subprocess.Popen([sys.executable,"child.py"])\n'
            + ending)
        script = '#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' launcher.py\n'
        if wrapper == 'run_phase':
            (copy / 'check.sh').write_text(script)
        else:
            lake = copy / 'bin/lake'
            lake.write_text(script)
            lake.chmod(0o755)
        bootstrap = (
            'import sys,runpy;sys.path.insert(0,"tools");import bounded_process;'
            'original=bounded_process.run_bounded;'
            'bounded_process.run_bounded=lambda command,**kw: '
            'original(command,cwd=kw["cwd"],timeout=0.75);'
            'sys.argv=["tools/' + wrapper + '.py","build","0"];'
            'runpy.run_path("tools/' + wrapper + '.py",run_name="__main__")')
        import os
        env = os.environ.copy()
        env['PATH'] = str(copy / 'bin') + os.pathsep + env.get('PATH', '')
        childrun = subprocess.Popen([sys.executable, '-B', '-c', bootstrap], cwd=copy,
                                    env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        deadline = time.monotonic() + 5
        while not (copy / 'child-ready').exists() and childrun.poll() is None and time.monotonic() < deadline:
            time.sleep(0.01)
        assert (copy / 'child-ready').exists(), wrapper + ': child startup was not established'
        stdout, stderr = childrun.communicate(timeout=5)
        expected_exit = 124 if case == 'timeout' else 7 if case == 'ordinary_failure' else 0
        assert childrun.returncode == expected_exit, (wrapper, case, stdout, stderr)
        assert ('UNKNOWN' in stderr) == (case == 'timeout'), (wrapper, case, stderr)
        assert not (copy / 'receipts/final-receipt.json').exists()
        (copy / 'permit-write').write_text('go')
        time.sleep(0.4)
        assert not (copy / 'child-marker').exists(), wrapper + ': descendant survived ' + case
        failure_name = 'final-failure.json' if wrapper == 'run_phase' else 'setup-failure.json'
        if case == 'timeout':
            assert json.loads((copy / 'receipts' / failure_name).read_text())['result'] == 'UNKNOWN'
        else:
            assert not (copy / 'receipts' / failure_name).exists()
        results[wrapper + '_handshake_descendant_' + case] = 'CHILD_STARTED_AND_TERMINATED_NO_MARKER'
print(json.dumps({'result': 'PASS_CONTROLS_ONLY', 'checks': results}, indent=2, sort_keys=True))
