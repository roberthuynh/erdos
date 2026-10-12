#!/usr/bin/env python3
"""Manifest an explicit public file allowlist; reject unapproved additions."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
POLICY_NAME = 'public-export-policy.json'
IGNORED_DIRECTORIES = {'.lake', '.git', '__pycache__', 'runtime', 'cache', 'artifacts'}
PRIVATE_MARKERS = tuple(value.encode() for value in ('/' + 'Users/', 'reports/' + '585-', 'reports/' + '585/'))
COMPILED_SUFFIXES = {'.pyc', '.pyo', '.olean', '.ilean', '.trace', '.o', '.a', '.so', '.dylib', '.dll', '.exe'}


def relative_name(value):
    """Accept only canonical relative file names, never patterns or traversal."""
    if (not isinstance(value, str) or not value or '\\' in value
            or any(ord(c) < 32 for c in value) or any(c in value for c in '*?[]')):
        raise ValueError(f'Invalid public policy path: {value!r}')
    path = PurePosixPath(value)
    if path.is_absolute() or '..' in path.parts or str(path) != value or ':' in value:
        raise ValueError(f'Invalid public policy path: {value!r}')
    if any(part in IGNORED_DIRECTORIES for part in path.parts) or path.suffix in COMPILED_SUFFIXES:
        raise ValueError(f'Runtime or compiled path cannot be approved: {value}')
    return value


def load_policy(root, policy=None):
    if policy is None or isinstance(policy, (str, Path)):
        path = root / POLICY_NAME if policy is None else Path(policy)
        if path.is_symlink():
            raise ValueError('Public export policy must not be a symlink')
        if not path.is_file():
            raise ValueError(f'Public export policy required: {POLICY_NAME}')
        policy = json.loads(path.read_text())
    if not isinstance(policy, dict) or policy.get('schema_version') != 1:
        raise ValueError('Unsupported public export policy schema')
    approved = policy.get('allowed_files')
    excluded = policy.get('excluded_files', [])
    if not isinstance(approved, list) or not isinstance(excluded, list):
        raise ValueError('Public policy requires explicit allowed_files and excluded_files lists')
    allowed = {relative_name(p) for p in approved}
    omitted = {relative_name(p) for p in excluded}
    if not allowed or len(allowed) != len(approved) or len(omitted) != len(excluded):
        raise ValueError('Empty or duplicate public policy paths')
    if allowed & omitted:
        raise ValueError('Public policy allowlist overlaps exclusions')
    required = policy.get('required_files', [])
    if not isinstance(required, list):
        raise ValueError('Public policy required_files must be a list')
    required_set = {relative_name(p) for p in required}
    if len(required_set) != len(required) or not required_set <= allowed:
        raise ValueError('Required paths must be unique approved paths')
    public_blobs = policy.get('public_baseline_blobs', {})
    exemptions = policy.get('content_scan_exemptions', [])
    if not isinstance(public_blobs, dict) or not isinstance(exemptions, list):
        raise ValueError('Invalid public provenance or fixture exemptions')
    if any(relative_name(p) not in allowed or not isinstance(value, str)
           or len(value) != 40 or any(c not in '0123456789abcdef' for c in value)
           for p, value in public_blobs.items()):
        raise ValueError('Invalid public baseline blob identity')
    exempt_set = {relative_name(p) for p in exemptions}
    if len(exempt_set) != len(exemptions) or not exempt_set <= allowed:
        raise ValueError('Fixture exemptions must be unique approved paths')
    return allowed, omitted, required_set, public_blobs, exempt_set


def check_content(path, relative, public_blobs, exemptions):
    """Historical public bytes are retained; scan changed and new file contents."""
    if relative in exemptions:
        return
    identity = hashlib.sha1(f'blob {path.stat().st_size}\0'.encode())
    private_path = False
    overlap = b''
    with path.open('rb') as source:
        while chunk := source.read(1024 * 1024):
            identity.update(chunk)
            combined = overlap + chunk
            private_path |= any(marker in combined for marker in PRIVATE_MARKERS)
            overlap = combined[-64:]
    if identity.hexdigest() == public_blobs.get(relative):
        return
    if private_path:
        raise ValueError(f'Private source path in new or changed public file: {relative}')


def export_files(root=ROOT, exclude=None, policy=None):
    """List approved existing files; explicit fixtures may provide their own policy."""
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('Export root must be an existing directory, not a symlink')
    root = root.absolute()
    allowed, omitted, required, public_blobs, exemptions = load_policy(root, policy)
    # Only the exact manifest output may be omitted by the caller.
    output = Path(exclude).absolute() if exclude is not None else None
    directories = {str(parent) for p in allowed | omitted for parent in PurePosixPath(p).parents}
    files = []
    for current, dirs, names in os.walk(root, followlinks=False):
        current = Path(current)
        for name in list(dirs):
            path = current / name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                raise ValueError(f'Symlink cannot be exported: {relative}')
            if name in IGNORED_DIRECTORIES:
                dirs.remove(name)
            elif relative not in directories:
                raise ValueError(f'Unapproved export directory: {relative}')
        for name in names:
            path = current / name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                raise ValueError(f'Symlink cannot be exported: {relative}')
            if path.suffix in COMPILED_SUFFIXES:
                continue
            if path == output or relative in omitted:
                continue
            if relative not in allowed:
                raise ValueError(f'Unapproved export file: {relative}')
            if not path.is_file():
                raise ValueError(f'Nonregular export file: {relative}')
            check_content(path, relative, public_blobs, exemptions)
            files.append(path)
    missing = required - {p.relative_to(root).as_posix() for p in files}
    if missing:
        raise ValueError(f'Required public files missing: {sorted(missing)}')
    return sorted(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--policy', type=Path, help='Explicit policy; defaults to public-export-policy.json')
    args = parser.parse_args()
    output = args.output.absolute()
    if output.is_symlink():
        raise ValueError('Manifest output must not be a symlink')
    files = export_files(exclude=output, policy=args.policy)
    manifest = {'algorithm': 'sha256', 'policy': POLICY_NAME,
                'excluded': ['runtime/cache directories', 'compiled files', 'explicit policy exclusions', 'output manifest itself'],
                'files': [{'path': p.relative_to(ROOT.absolute()).as_posix(), 'bytes': p.stat().st_size, 'mode': oct(p.stat().st_mode & 0o777),
                           'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]}
    output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(f'EXPORT MANIFEST: {len(files)} files')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        raise SystemExit(f'EXPORT MANIFEST: FAIL: {error}')
