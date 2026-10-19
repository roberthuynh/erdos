"""Toolchain pins for check-clean.sh (B4, toolchain part).
  make:   python3 -I toolchain_pins.py make   TOOLCHAIN_DIR OUT
  verify: python3 -I toolchain_pins.py verify TOOLCHAIN_DIR PINS
Covers `bin/` (lean, lake, leanchecker, ...) and `lib/lean/` (libleanshared, the kernel and runtime, and every
Init/Std/Lean/Lake `.olean` part). PINS was made from the official release asset lean-4.33.1-darwin_aarch64.tar.zst
(SHA-256 88c45aad985b5d2a8d925fe10bd1296bd35f66f408480ab182d3facccd065a9d, GitHub's published digest); see
../TRUST-BASE.md. verify fails on a missing, extra or changed file under those two directories."""
import hashlib
import os
import sys

PREFIXES = ('bin/', 'lib/lean/')


def tree(root):
    res = {}
    for d, dirs, fs in os.walk(root):
        for f in fs:
            p = os.path.join(d, f)
            rel = os.path.relpath(p, root)
            if not rel.startswith(PREFIXES):
                continue
            if os.path.islink(p):
                res[rel] = 'link:' + os.readlink(p)
                continue
            h = hashlib.sha256()
            with open(p, 'rb') as fh:
                for chunk in iter(lambda: fh.read(1 << 22), b''):
                    h.update(chunk)
            res[rel] = h.hexdigest()
    return res


if __name__ == '__main__':
    mode, root, pins = sys.argv[1], sys.argv[2], sys.argv[3]
    have = tree(root)
    if mode == 'make':
        with open(pins, 'w') as out:
            for rel in sorted(have):
                out.write(f'{have[rel]}  {rel}\n')
        print(f'TOOLCHAINPINS made {len(have)} files')
        sys.exit(0)
    want = dict(reversed(line.rstrip('\n').split('  ', 1)) for line in open(pins))
    missing = [r for r in want if r not in have]
    extra = [r for r in have if r not in want]
    differ = [r for r in want if r in have and have[r] != want[r]]
    ok = not missing and not extra and not differ
    print(f"TOOLCHAINPINS {'ok' if ok else 'FAIL'} pinned={len(want)} present={len(have)} missing={len(missing)} "
          f"extra={len(extra)} differ={len(differ)} sample={(missing + extra + differ)[:3]}")
    sys.exit(0 if ok else 1)
