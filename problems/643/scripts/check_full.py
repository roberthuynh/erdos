#!/usr/bin/env python3
"""Frozen complete module audit. Every Lean invocation is bounded at 240 seconds."""
import argparse,hashlib,json,re,subprocess,sys,tomllib
from pathlib import Path
from source_scan import lean_code,DISALLOWED
ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT
ALLOWED={'propext','Classical.choice','Quot.sound'}
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def inventory(project=None):
 # Lake's default Openmath library covers Openmath.lean and Openmath/**/*.lean.
 # Separately checked projects and archived sources have independent namespaces.
 project=PROJECT if project is None else project
 config=tomllib.loads((project/'lakefile.toml').read_text())
 if config.get('lean_lib')!=[{'name':'Openmath'}]:
  raise ValueError('Legacy Lean library configuration changed; review inventory adapter')
 files=[project/'Openmath.lean',*sorted((project/'Openmath').rglob('*.lean'))]
 if any(p.is_symlink() for p in files):raise ValueError('Symlink in configured Lean sources')
 return {str(p.relative_to(project)).removesuffix('.lean').replace('/','.'): {'source':str(p.relative_to(project)), 'sha256':digest(p)} for p in files}
def identities():
 result=inventory()
 for item in result.values():
  if re.search(DISALLOWED,lean_code((PROJECT/item['source']).read_text())): raise ValueError('disallowed proof token: '+item['source'])
 result['$pins']={p:digest(PROJECT/p) for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
 return result
def run(args,source=None):
 p=subprocess.run(['timeout','240',*args],cwd=PROJECT,input=source,capture_output=True,text=True)
 if p.returncode == 124:
  print('UNKNOWN: Lean command exceeded 240 seconds',file=sys.stderr)
  raise SystemExit(124)
 if p.returncode:
  print(p.stdout,end='');print(p.stderr,end='',file=sys.stderr)
  raise subprocess.CalledProcessError(p.returncode,args)
 return p.stdout

def audit(module):
 source=f'import {module}\nimport Lean\n' + '''run_elab do
 let env ← Lean.getEnv
 for (name, info) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? name then
   if env.header.moduleNames[idx.toNat]! == MODULE then
    let ty ← Lean.Meta.ppExpr info.type
    let ax ← Lean.collectAxioms name
    Lean.logInfo (Lean.Json.compress (Lean.Json.mkObj [("declaration",Lean.toJson name.toString),("type",Lean.toJson ty.pretty),("axioms",Lean.toJson (ax.map Lean.Name.toString))]))
'''.replace('MODULE','`'+module)
 output=run(['lake','env','lean','--stdin'],source)
 records=[json.loads(line) for line in output.splitlines() if line.startswith('{')]
 unexpected=[line for line in output.splitlines() if line and not line.startswith('{')]
 if unexpected: raise ValueError('unexpected Lean audit output: '+str(unexpected))
 names=[r['declaration'] for r in records]
 if len(names)!=len(set(names)): raise ValueError('duplicate declarations')
 for r in records:
  bad=set(r['axioms'])-ALLOWED
  if bad: raise ValueError(f"{r['declaration']}: disallowed axioms {bad}")
 return sorted(records,key=lambda r:r['declaration'])