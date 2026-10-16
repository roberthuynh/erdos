#!/usr/bin/env python3
"""Validate collection navigation, declared packages and preserved author prose."""
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit
from check import ROOT, load_registry


def prose(text):
    # Link destinations change during relocation; the visible words do not.
    return re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', text).strip()


def heading_ids(text):
    """GitHub-style ATX heading anchors used by the collection documents."""
    ids=set();counts={};fence=None
    for line in text.splitlines():
        marker=re.match(r'^\s*(`{3,}|~{3,})',line)
        if marker:
            char=marker.group(1)[0]
            if fence is None:fence=char
            elif fence==char:fence=None
            continue
        if fence:continue
        match=re.match(r'^ {0,3}#{1,6}\s+(.+?)\s*#*$',line)
        if not match:continue
        label=re.sub(r'<[^>]*>','',prose(match.group(1))).lower()
        slug=''.join(c for c in label if c.isalnum() or c in '_- ').replace(' ','-')
        count=counts.get(slug,0);counts[slug]=count+1
        ids.add(slug if count==0 else f'{slug}-{count}')
    return ids


def check_collection(root=ROOT):
    registry=load_registry(root)
    documents=[root/'README.md',root/'CONTRIBUTING.md',*sorted((root/'docs').glob('*.md'))]
    for item in registry.values():
        documents.extend([root/item['path']/'README.md',root/item['path']/'RESULTS.md'])
        if f"({item['path']}/README.md)" not in (root/'README.md').read_text():
            raise ValueError('Catalogue omits registered problem')
    count=0
    for path in documents:
        for target in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',path.read_text()):
            parsed=urlsplit(target.strip('<>'))
            if parsed.scheme or parsed.netloc: continue
            destination=(path.parent/unquote(parsed.path)).resolve() if parsed.path else path.resolve()
            if not destination.is_relative_to(root.resolve()) or not destination.is_file():
                raise ValueError(f'Broken local link: {path.relative_to(root)} -> {target}')
            if parsed.fragment and destination.suffix.lower()=='.md' and unquote(parsed.fragment) not in heading_ids(destination.read_text()):
                raise ValueError(f'Broken local fragment: {path.relative_to(root)} -> {target}')
            count+=1
    protected=json.loads((root/'scripts/author-prose.json').read_text())
    for item in protected['files']:
        if hashlib.sha256((root/item['path']).read_bytes()).hexdigest()!=item['sha256']:
            raise ValueError('Protected findings text changed: '+item['path'])
    for item in protected['blocks']:
        text=(root/item['path']).read_text()
        if text.count(item['start'])!=1: raise ValueError('Protected prose start missing or ambiguous')
        body=text.split(item['start'],1)[1]
        if item['end']:
            if item['end'] not in body: raise ValueError('Protected prose end missing')
            body=body.split(item['end'],1)[0]
        if hashlib.sha256(prose(body).encode()).hexdigest()!=item['sha256']:
            raise ValueError('Protected author prose changed: '+item['label'])
    print(f'COLLECTION: PASS ({len(registry)} problems, {count} local links, {len(protected["files"])} protected files, {len(protected["blocks"])} author blocks)')
    return count

if __name__=='__main__':
    try:check_collection()
    except (ValueError,KeyError,OSError) as error: raise SystemExit(f'COLLECTION: FAIL: {error}')
