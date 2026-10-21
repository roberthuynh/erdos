#!/usr/bin/env python3
"""Fetch the pinned Lake dependencies/cache; not a theorem check."""
from pathlib import Path
import json
import subprocess
import sys
from bounded_process import run_bounded, JobCancelled
ROOT = Path(__file__).resolve().parents[1]
RECEIPTS = ROOT / 'receipts'
(RECEIPTS / 'final-receipt.json').unlink(missing_ok=True)
try:
    result = run_bounded(['lake', 'exe', 'cache', 'get'], cwd=ROOT, timeout=240)
    if result.returncode:
        raise SystemExit(result.returncode)
    print('SETUP COMPLETE; strict pin and theorem checks remain required')
except (subprocess.TimeoutExpired, JobCancelled) as exc:
    RECEIPTS.mkdir(exist_ok=True)
    (RECEIPTS / 'setup-failure.json').write_text(json.dumps({
        'result': 'UNKNOWN', 'error': str(exc) if isinstance(exc, JobCancelled) else 'outer timeout 240s'}) + '\n')
    print('SETUP UNKNOWN: ' + ('cancelled' if isinstance(exc, JobCancelled) else 'timeout 240s'), file=sys.stderr)
    raise SystemExit(128 + exc.signum if isinstance(exc, JobCancelled) else 124)
