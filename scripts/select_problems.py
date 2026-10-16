#!/usr/bin/env python3
"""Select affected packages for CI; shared check changes select every package."""
import argparse
import json
import subprocess
from check import ROOT, load_registry


def select(registry, paths=None):
    if paths is None:
        selected = set(registry)
    else:
        selected = set()
        for path in paths:
            parts = path.split('/')
            if len(parts) >= 3 and parts[0] == 'problems':
                if parts[1] in registry:
                    selected.add(parts[1])
            elif not (path.endswith('.md') or path.startswith('docs/') or
                      path in {'LICENSE', 'NOTICE', 'CITATION.cff'}):
                selected.update(registry)
    return {'include': [{'id': identifier, 'lean': 'lean' in registry[identifier]}
                        for identifier in sorted(selected)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base')
    args = parser.parse_args()
    registry = load_registry()
    paths = None
    if args.base and set(args.base) != {'0'}:
        subprocess.run(['git', 'rev-parse', '--verify', args.base + '^{commit}'],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        result = subprocess.run(['git', 'diff', '--name-only', '-z', '--no-renames',
                                 args.base, 'HEAD', '--'], cwd=ROOT, check=True,
                                capture_output=True)
        paths = result.stdout.decode().rstrip('\0').split('\0') if result.stdout else []
    print(json.dumps(select(registry, paths), separators=(',', ':')))


if __name__ == '__main__':
    main()
