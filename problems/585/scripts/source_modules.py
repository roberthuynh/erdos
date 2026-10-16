#!/usr/bin/env python3
"""Enumerate configured custom Lean sources and check transitive root coverage."""
import argparse
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parent.parent


def source_modules(root=ROOT):
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    modules = {}
    for library in config.get('lean_lib', []):
        name = library['name']
        globs = library.get('globs', [name, name + '.+'])
        for glob in globs:
            if glob.endswith('.+'):
                directory = root / glob[:-2].replace('.', '/')
                files = directory.rglob('*.lean') if directory.is_dir() else []
            elif re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', glob):
                path = root / (glob.replace('.', '/') + '.lean')
                files = [path] if path.is_file() else []
            else:
                raise ValueError(f'Unsupported Lean source glob: {glob}')
            for path in files:
                relative = path.relative_to(root)
                if any(part in {'.lake', '__pycache__', '.git'} for part in relative.parts):
                    continue
                module = relative.with_suffix('').as_posix().replace('/', '.')
                modules[module] = path
    if not modules:
        raise ValueError('No configured custom Lean modules')
    return dict(sorted(modules.items()))


def imports(path):
    from check_axioms import lean_code
    return [module for line in lean_code(path.read_text()).splitlines()
            if re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+', line)
            for module in re.sub(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+', '', line).split()]


def check_coverage(root=ROOT):
    modules = source_modules(root)
    pending = ['Openmath']
    seen = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        if module not in modules:
            raise ValueError(f'Root imports an unconfigured custom module: {module}')
        seen.add(module)
        for child in imports(modules[module]):
            if child in modules:
                pending.append(child)
            elif (root / (child.replace('.', '/') + '.lean')).is_file():
                raise ValueError(f'Unconfigured local import: {child}')
    missing = sorted(set(modules) - seen)
    if missing:
        raise ValueError(f'Custom modules outside transitive Openmath root closure: {missing}')
    return modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true', help='Print one module per line for kernel replay')
    args = parser.parse_args()
    modules = check_coverage()
    if args.list:
        print('\n'.join(modules))
    else:
        print(f'SOURCE COVERAGE: PASS ({len(modules)} configured modules in transitive root closure)')


if __name__ == '__main__':
    main()
