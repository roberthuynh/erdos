"""Toolchain artifact pins for the phased verifier.
  make:   python3 -I toolchain_pins.py make   TOOLCHAIN_DIR OUT
  verify: python3 -I toolchain_pins.py verify TOOLCHAIN_DIR PINS
Covers `bin/` (lean, lake, leanchecker, ...) and `lib/lean/` (libleanshared, the kernel and runtime, and every
Init/Std/Lean/Lake `.olean` part). PINS was made from the official release asset lean-4.33.1-darwin_aarch64.tar.zst
(SHA-256 88c45aad985b5d2a8d925fe10bd1296bd35f66f408480ab182d3facccd065a9d, GitHub's published digest); see
../TRUST-BASE.md. verify fails on a missing, extra or changed file under those two directories, or any symbolic
link in either covered tree or its path beneath TOOLCHAIN_DIR."""
import hashlib
import os
import sys

PREFIXES = ('bin/', 'lib/lean/')


def raise_walk_error(error):
    raise error


def tree(root):
    res = {}
    root = os.path.abspath(root)
    # Check each ancestor explicitly: os.walk neither follows directory links
    # nor reports an absent/dangling walk root as an error.
    for rel in ('', 'bin', 'lib', 'lib/lean'):
        path = os.path.join(root, rel) if rel else root
        if os.path.islink(path):
            raise ValueError('symbolic link in covered tree: ' + path)
    for prefix in PREFIXES:
        base = os.path.join(root, prefix.rstrip('/'))
        for d, dirs, fs in os.walk(base, onerror=raise_walk_error):
            for name in dirs + fs:
                p = os.path.join(d, name)
                if os.path.islink(p):
                    raise ValueError('symbolic link in covered tree: ' + p)
            for f in fs:
                p = os.path.join(d, f)
                rel = os.path.relpath(p, root)
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
