#!/usr/bin/env python3
"""Complete environment declaration inventory, frozen types and axiom closures."""
import argparse,json
from check_full import ROOT,run,identities,ALLOWED
from source_modules import check_coverage
from source_scan import lean_code

def collect():
 modules=check_coverage()
 source=''.join(f'import {m}\n' for m in modules)+'import Lean\n'
 source += 'run_elab do\n let env ← Lean.getEnv\n let modules : Array Lean.Name := #['+','.join('`'+m for m in modules)+']\n'
 source += ' for (name, info) in env.constants.toList do\n  if let some idx := env.getModuleIdxFor? name then\n   let module := env.header.moduleNames[idx.toNat]!\n   if modules.contains module then\n    let ty ← Lean.Meta.ppExpr info.type\n    let ax ← Lean.collectAxioms name\n    Lean.logInfo (Lean.Json.compress (Lean.Json.mkObj [("module",Lean.toJson module.toString),("declaration",Lean.toJson name.toString),("type",Lean.toJson ty.pretty),("axioms",Lean.toJson (ax.map Lean.Name.toString))]))\n'
 output=run(['lake','env','lean','--stdin'],source)
 records=[json.loads(l) for l in output.splitlines() if l.startswith('{')]
 if any(l and not l.startswith('{') for l in output.splitlines()): raise ValueError('unexpected audit output')
 if not records or len({r['declaration'] for r in records})!=len(records):raise ValueError('empty or duplicated inventory')
 identity=json.loads((ROOT/'source-identity.json').read_text())
 for r in records:
  if set(r['axioms'])-ALLOWED: raise ValueError('disallowed axioms '+r['declaration'])
  r['axioms']=sorted(r['axioms']);r['oracle']=r['declaration'] in identity['declarations']
 return sorted(records,key=lambda r:(r['module'],r['declaration']))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--register',action='store_true');a=p.parse_args()
 current=identities();manifest=ROOT/'scripts/proof-modules.json';registry=ROOT/'scripts/headline-theorems.json'
 if a.register: manifest.write_text(json.dumps(current,indent=2)+'\n')
 if json.loads(manifest.read_text())!=current: raise ValueError('frozen source/pin identity changed')
 records=collect()
 if a.register:registry.write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n');print(f'REGISTERED: {len(records)} declarations')
 else:
  if json.loads(registry.read_text())!=records:raise ValueError('declaration inventory, types or axioms changed')
  print(f'AXIOMS: PASS ({len(records)} declarations)');print(f'STATEMENTS: PASS ({len(records)} recorded types)')
