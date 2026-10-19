"""Resolve explicit or package-local dependencies; binary pins remain mandatory."""
import os
from pathlib import Path
import shutil
import subprocess


def discover(root):
    configured = os.environ.get('ERDOS643_TOOLCHAIN')
    if configured:
        prefix = Path(configured).expanduser().resolve()
    else:
        executable = shutil.which('lean')
        if not executable:
            raise RuntimeError('Lean unavailable: install the pinned lean-toolchain with elan')
        try:
            result = subprocess.run([executable, '--print-prefix'], cwd=root,
                                    check=True, capture_output=True, text=True, timeout=240)
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError('UNKNOWN timeout 240s: Lean toolchain discovery') from exc
        prefix = Path(result.stdout.strip()).resolve()
    lean = prefix / 'bin/lean'
    checker = prefix / 'bin/leanchecker'
    if not lean.is_file() or not checker.is_file():
        raise RuntimeError('resolved toolchain must contain bin/lean and bin/leanchecker')
    try:
        version = subprocess.run([str(lean), '--version'], check=True, capture_output=True,
                                 text=True, timeout=240).stdout
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError('UNKNOWN timeout 240s: Lean version check') from exc
    if not version.startswith('Lean (version 4.33.1,'):
        raise RuntimeError('resolved Lean version differs from lean-toolchain')
    packages = Path(os.environ.get('ERDOS643_PACKAGES', str(root / '.lake/packages'))).expanduser().resolve()
    return lean, checker, packages
