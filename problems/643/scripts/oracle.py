#!/usr/bin/env python3
"""Bounded fail-closed headline build, source and axiom oracle."""
import json,re,subprocess,sys
from pathlib import Path
from source_scan import lean_code, DISALLOWED
ROOT=Path(__file__).resolve().parents[1]
ALLOWED={"propext","Classical.choice","Quot.sound"}
def axioms(output, names):
 records=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",output)
 records += [(n,"") for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
 if len(records)!=len(names) or {n for n,_ in records}!=set(names):
  raise ValueError("missing, duplicate or unexpected axiom report")
 for n,a in records:
  bad={x.strip() for x in a.split(",") if x.strip()}-ALLOWED
  if bad: raise ValueError(f"{n}: disallowed axioms {sorted(bad)}")
def main():
 identity=json.loads((ROOT/'source-identity.json').read_text())
 file=sys.argv[1] if len(sys.argv)>1 else identity['root_module'].replace('.','/')+'.lean'
 name=sys.argv[2] if len(sys.argv)>2 else identity['declaration']
 module=file.removesuffix('.lean').replace('/','.')
 code=lean_code((ROOT/file).read_text())
 if re.search(DISALLOWED,code): raise ValueError("disallowed proof token")
 p=subprocess.run(['timeout','240','lake','build',module],cwd=ROOT,text=True,capture_output=True)
 print(p.stdout,end=''); print(p.stderr,end='',file=sys.stderr)
 if p.returncode: return p.returncode
 p=subprocess.run(['timeout','240','lake','env','lean','--stdin'],cwd=ROOT,input=f'import {module}\n#print axioms {name}\n',text=True,capture_output=True)
 print(p.stdout,end=''); print(p.stderr,end='',file=sys.stderr)
 if p.returncode: return p.returncode
 axioms(p.stdout,[name]); print('RESULT: PASS'); return 0
if __name__=='__main__':
 try:
  rc=main()
  if rc: print('RESULT: UNKNOWN' if rc==124 else 'RESULT: FAIL')
  sys.exit(rc)
 except (ValueError,OSError) as e:
  print(f'RESULT: FAIL: {e}',file=sys.stderr); sys.exit(1)
