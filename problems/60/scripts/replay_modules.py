#!/usr/bin/env python3
"""Replay configured custom modules through the kernel, stopping on any failure."""
import argparse
from pathlib import Path
import subprocess
import sys

from source_modules import check_coverage

ROOT = Path(__file__).resolve().parent.parent


def replay(root=ROOT, selected=None, run=subprocess.run):
    configured = check_coverage(root)
    modules = list(configured) if selected is None else list(selected)
    if not modules or len(modules) != len(set(modules)):
        raise ValueError('Kernel replay requires a nonempty, unique module list')
    if any(module not in configured for module in modules):
        raise ValueError('Requested kernel replay module is not configured')
    for module in modules:
        print(f'kernel replay {module}', flush=True)
        run(['timeout', '240', 'lake', 'env', 'lean', '--stdin'], cwd=root,
            input=f'import LeanChecker\n#eval replayFromImports "{module}".toName\n',
            text=True, check=True)
    print(f'KERNEL REPLAY: PASS ({len(modules)} of {len(configured)} configured modules)', flush=True)
    return len(modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--module', action='append', help='Replay only this configured module; repeatable')
    args = parser.parse_args()
    try:
        replay(selected=args.module)
    except subprocess.CalledProcessError as error:
        if error.returncode == 124:
            print(f'KERNEL REPLAY: UNKNOWN: {error}', file=sys.stderr)
            return 124
        print(f'KERNEL REPLAY: FAIL: {error}', file=sys.stderr)
        return 1
    except (ValueError, OSError) as error:
        print(f'KERNEL REPLAY: FAIL: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
