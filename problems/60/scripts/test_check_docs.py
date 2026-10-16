#!/usr/bin/env python3
"""Negative controls for source identity and broken links."""
import importlib.util,shutil,tempfile
from pathlib import Path
spec=importlib.util.spec_from_file_location('check_docs',Path(__file__).with_name('check_docs.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
with tempfile.TemporaryDirectory() as d:
    root=Path(d)/'problems/60';shutil.copytree(m.ROOT,root,ignore=shutil.ignore_patterns(".lake", "__pycache__"))
    (root.parent.parent/'README.md').write_text('test collection')
    (root.parent.parent/'CONTRIBUTING.md').write_text('test contribution guide')
    m.check(root)
    p=root/'LINEAR-RANGE-THEOREM.md';s=p.read_text();p.write_text(s+'changed')
    try:m.check(root)
    except ValueError as e:
        if 'identity mismatch' not in str(e):raise AssertionError(str(e))
    else:raise AssertionError('Changed proof accepted')
    p.write_text(s)
    (root/'FINDINGS.md').write_text('[missing](missing.md)')
    try:m.check(root)
    except ValueError as e:
        if 'Broken local link' not in str(e):raise AssertionError(str(e))
    else:raise AssertionError('Broken link accepted')
print('NEGATIVE CONTROLS: PASS (proof mutation and broken link rejected)')
