#!/usr/bin/env python3
"""Document identity and link checks only. Does not verify mathematics."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]

def headings(text):
    result, counts, fence = set(), {}, None
    for line in text.splitlines():
        marker = re.match(r'^\s*(`{3,}|~{3,})', line)
        if marker:
            char = marker.group(1)[0]
            if fence is None:
                fence = char
            elif fence == char:
                fence = None
            continue
        if fence:
            continue
        heading = re.match(r'^ {0,3}#{1,6}\s+(.+?)\s*#*$', line)
        if heading:
            label = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', heading.group(1)).lower()
            slug = ''.join(c for c in label if c.isalnum() or c in '_- ').replace(' ', '-')
            count = counts.get(slug, 0)
            counts[slug] = count + 1
            result.add(slug if count == 0 else f'{slug}-{count}')
    return result

def safe_manifest_file(root, name):
    if not isinstance(name, str) or not name or '\\' in name:
        raise ValueError('Unsafe manifest path')
    relative = PurePosixPath(name)
    if relative.is_absolute() or '..' in relative.parts or str(relative) != name:
        raise ValueError('Unsafe manifest path')
    path = root/name
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError('Missing/unsafe document: '+name)
    if any(part.is_symlink() for part in [path, *path.parents] if part == root or root in part.parents):
        raise ValueError('Missing/unsafe document: '+name)
    return path

def check(root=ROOT):
    expected = json.loads((root/'document-hashes.json').read_text())
    if not isinstance(expected, dict) or any(not isinstance(digest, str) or
            not re.fullmatch(r'[0-9a-f]{64}', digest) for digest in expected.values()):
        raise ValueError('Invalid document hash manifest')
    for name in expected:
        safe_manifest_file(root, name)
    if any(path.is_symlink() for path in root.rglob('*') if '.lake' not in path.relative_to(root).parts):
        raise ValueError('Symlink in document package')
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and '.lake' not in p.relative_to(root).parts}
    if actual != set(expected) | {'document-hashes.json'}:
        raise ValueError('Unlisted or missing package file')
    for name, digest in expected.items():
        path = safe_manifest_file(root, name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('Document identity mismatch: '+name)
    for path in root.glob('*.md'):
        for target in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',path.read_text()):
            parsed = urlsplit(target.strip('<>'))
            if parsed.scheme or parsed.netloc:
                continue
            dest = (path.parent/unquote(parsed.path)).resolve() if parsed.path else path.resolve()
            if not dest.is_relative_to(root.parents[1].resolve()) or not dest.is_file():
                raise ValueError('Broken/escaping local link: '+target)
            if parsed.fragment and dest.suffix == '.md':
                if unquote(parsed.fragment) not in headings(dest.read_text()):
                    raise ValueError('Broken local fragment: '+target)
    print('DOCUMENTS: PASS (identity and links only; no mathematical verification)')

if __name__ == '__main__':
    try:
        check()
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit('DOCUMENTS: FAIL: '+str(error))
