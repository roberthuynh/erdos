#!/usr/bin/env python3
"""Documentation-only link and source-identity checks; no mathematical certification."""
import hashlib,json,re,sys
from pathlib import Path
from urllib.parse import urlsplit,unquote
ROOT=Path(__file__).resolve().parent.parent

def check(root=ROOT):
    manifest=json.loads((root/'source-identity.json').read_text())
    expected={'CORE-AND-RETAINED-PATHS.md','COUNT-BASED-COMPLETION.md','LINEAR-RANGE-THEOREM.md','LINEAR-SUPPORT-THEOREM.md','LITERATURE-COMPARISON.md','LOCALIZATION-ARGUMENT.md','README.md','SOURCES.md'}
    records=manifest['files']
    if len(records)!=8 or {x['file'] for x in records}!=expected:raise ValueError('Frozen eight-file identity manifest incomplete')
    for item in records:
        if hashlib.sha256((root/item['file']).read_bytes()).hexdigest()!=item['export_sha256']:raise ValueError('Source identity mismatch: '+item['file'])
    count=0
    for p in root.glob('*.md'):
        for target in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',p.read_text()):
            link=urlsplit(target)
            if link.scheme or link.netloc or not link.path:continue
            destination=(p.parent/unquote(link.path)).resolve()
            if not destination.is_relative_to(root.parent.parent.resolve()) or not destination.is_file():raise ValueError('Broken local link: '+p.name+' -> '+target)
            count+=1
    print(f'DOCUMENTATION ONLY: PASS (8 source identities, {count} local file links). NO MATHEMATICAL CERTIFICATION; NO LEAN CHECK; NO NOVELTY OR HUMAN-REVIEW CLEARANCE.')
    return count
if __name__=='__main__':
    try:check()
    except (ValueError,KeyError,OSError) as e:print('DOCUMENTATION ONLY: FAIL: '+str(e),file=sys.stderr);sys.exit(1)
