#!/usr/bin/env python3
"""All configured custom sources, requiring aggregate transitive coverage."""
import argparse,re
from check_full import ROOT,inventory
from source_scan import lean_code
def check_coverage(root=ROOT):
 modules={m:root/v['source'] for m,v in inventory().items()}
 todo=['Erdos1017.SharpAffine','Erdos1017.MesoscopicLower','Erdos1017.BinomialSharp','Erdos1017.SlopeBarrier','Erdos1017.NearComplete'];seen=set()
 while todo:
  m=todo.pop()
  if m in seen: continue
  seen.add(m)
  for line in lean_code(modules[m].read_text()).splitlines():
   match=re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$',line)
   if match: todo.extend(c for c in match[1].split() if c in modules)
 if seen!=set(modules): raise ValueError('modules outside aggregate closure: '+str(set(modules)-seen))
 return modules
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--list',action='store_true');a=p.parse_args();m=check_coverage()
 print('\n'.join(m) if a.list else f'SOURCE COVERAGE: PASS ({len(m)} configured modules)')
