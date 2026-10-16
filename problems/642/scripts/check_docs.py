#!/usr/bin/env python3
"""Validate frozen project sources, public artifacts and in-collection Markdown links."""
from pathlib import Path, PurePosixPath
import hashlib,json,re
from urllib.parse import urlsplit,unquote
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def headings(text):
 result=set();counts={};fence=None
 for line in text.splitlines():
  mark=re.match(r'^\s*(`{3,}|~{3,})',line)
  if mark:
   char=mark.group(1)[0]
   if fence is None:fence=char
   elif fence==char:fence=None
   continue
  if fence:continue
  h=re.match(r'^ {0,3}#{1,6}\s+(.+?)\s*#*$',line)
  if h:
   label=re.sub(r'\[([^\]]+)\]\([^)]+\)',r'\1',h.group(1)).lower()
   slug=''.join(c for c in label if c.isalnum() or c in '_- ').replace(' ','-')
   i=counts.get(slug,0);counts[slug]=i+1;result.add(slug if not i else f'{slug}-{i}')
 return result
def safe(root,value):
 p=PurePosixPath(value)
 if p.is_absolute() or '..' in p.parts or '\\' in value or str(p)!=value:raise ValueError('Unsafe manifest path')
 q=root/value
 if not q.is_file() or q.is_symlink() or not q.resolve().is_relative_to(root.resolve()):raise ValueError('Missing/unsafe artifact: '+value)
 return q
def check(root=ROOT):
 identity=json.loads((root/'source-identity.json').read_text())
 expected={row['path']:row['sha256'] for row in identity['project_sources'].values()}
 actual={str(f.relative_to(root)) for f in (root/'Openmath').rglob('*.lean')}
 if actual!=set(expected):raise ValueError('Project source closure differs from manifest')
 for path,digest in expected.items():
  if sha(safe(root,path))!=digest:raise ValueError('Source hash mismatch: '+path)
 artifacts=identity.get('artifact_hashes',{})
 if not artifacts:raise ValueError('Missing public artifact identities')
 for path,digest in artifacts.items():
  if sha(safe(root,path))!=digest:raise ValueError('Artifact hash mismatch: '+path)
 if {p.name for p in root.glob('*.md')}-{p for p in artifacts if '/' not in p}:raise ValueError('Unregistered document')
 links=0;collection=root.parents[1].resolve()
 for file in root.glob('*.md'):
  for raw in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)',file.read_text()):
   u=urlsplit(raw.strip('<>'))
   if u.scheme or u.netloc:continue
   dest=(file.parent/unquote(u.path)).resolve() if u.path else file.resolve()
   if not dest.is_relative_to(collection) or not dest.is_file():raise ValueError(f'Broken/escaping local link: {file.name}: {raw}')
   if u.fragment and dest.suffix=='.md' and unquote(u.fragment) not in headings(dest.read_text()):raise ValueError('Broken fragment: '+raw)
   links+=1
 print(f'DOCS: PASS ({len(expected)} proof sources, {len(artifacts)} artifacts, {links} local links)')
if __name__=='__main__':
 try:check()
 except (ValueError,OSError,KeyError,TypeError) as e:raise SystemExit('DOCS: FAIL: '+str(e))
