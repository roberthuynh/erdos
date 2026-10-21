"""Olean pins for check-clean.sh (B2/B4).
  make:   python3 -I olean_pins.py make   PKROOT OUT   (record sha256 of every module data file Lean loads)
  verify: python3 -I olean_pins.py verify PKROOT PINS  (every pinned file present with the pinned sha256, and no
          extra module data file in any pinned package's build tree, so nothing can be planted or swapped)
Module data files: .olean, .olean.server, .olean.private under <pkg>/.lake/build/lib/lean for the packages of
standalone/lake-manifest.json. PINS was made from a fresh official Mathlib cache download (TRUST-BASE.md)."""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, '..', 'standalone', 'lake-manifest.json')
KINDS = ('.olean', '.olean.server', '.olean.private')


def packages():
    return [p['name'] for p in json.load(open(MANIFEST))['packages']]


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 22), b''):
            h.update(chunk)
    return h.hexdigest()


def files(pkroot):
    res = {}
    for pkg in packages():
        base = os.path.join(pkroot, pkg, '.lake', 'build', 'lib', 'lean')
        for d, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(KINDS):
                    p = os.path.join(d, f)
                    res[pkg + '/' + os.path.relpath(p, base)] = p
    return res


if __name__ == '__main__':
    mode, pkroot, pins = sys.argv[1], sys.argv[2], sys.argv[3]
    have = files(pkroot)
    if mode == 'make':
        with open(pins, 'w') as out:
            for rel in sorted(have):
                out.write(f'{sha(have[rel])}  {rel}\n')
        print(f'PINS made {len(have)} files')
        sys.exit(0)
    want = {}
    for line in open(pins):
        h, rel = line.rstrip('\n').split('  ', 1)
        want[rel] = h
    missing = [r for r in want if r not in have]
    extra = [r for r in have if r not in want]
    differ = [r for r in want if r in have and sha(have[r]) != want[r]]
    ok = not missing and not extra and not differ
    print(f"OLEANPINS {'ok' if ok else 'FAIL'} pinned={len(want)} present={len(have)} missing={len(missing)} "
          f"extra={len(extra)} differ={len(differ)} sample={(missing + extra + differ)[:3]}")
    sys.exit(0 if ok else 1)
