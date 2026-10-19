#!/usr/bin/env python3
"""Run exactly one official phase with an outer 240-second limit."""
import json
from pathlib import Path
import subprocess
import sys
from bounded_process import run_bounded, JobCancelled
ROOT = Path(__file__).resolve().parents[1]
(ROOT / 'receipts/final-receipt.json').unlink(missing_ok=True)
try:
    result = run_bounded(['sh', str(ROOT / 'check.sh'), *sys.argv[1:]], cwd=ROOT, timeout=240)
    raise SystemExit(result.returncode)
except (subprocess.TimeoutExpired, JobCancelled) as exc:
    receipts = ROOT / 'receipts'
    receipts.mkdir(exist_ok=True)
    (receipts / 'final-receipt.json').unlink(missing_ok=True)
    (receipts / 'final-failure.json').write_text(json.dumps({
        'result': 'UNKNOWN', 'phase': sys.argv[1:],
        'error': str(exc) if isinstance(exc, JobCancelled) else 'outer timeout 240s'}) + '\n')
    print('RESULT: UNKNOWN ' + ('cancelled' if isinstance(exc, JobCancelled) else 'outer timeout 240s'), file=sys.stderr)
    raise SystemExit(128 + exc.signum if isinstance(exc, JobCancelled) else 124)
