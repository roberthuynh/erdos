"""Print the `Openmath.*` imports of a Lean file, after removing comments and literals (srcscan.strip), so a
commented-out import is never followed. Usage: python3 -I imports.py FILE"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from srcscan import strip  # noqa: E402

code = strip(open(sys.argv[1], encoding='utf-8').read())
for m in re.findall(r"^\s*import\s+(Openmath\.\S+)", code, flags=re.M):
    print(m)
