#!/usr/bin/env python3
import argparse
from check_full import run
from source_modules import check_coverage
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--module',action='append');a=p.parse_args();configured=check_coverage()
 for m in a.module or configured:
  if m not in configured: raise ValueError('unconfigured module')
  print(run(['lake','env','lean','--stdin'],f'import LeanChecker\n#eval replayFromImports "{m}".toName\n'),end='')
 print('KERNEL REPLAY: PASS')
