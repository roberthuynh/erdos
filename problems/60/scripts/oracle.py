#!/usr/bin/env python3
"""Build and audit exactly one registered declaration, with bounded subprocesses."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
from check_axioms import ALLOWED, ROOT, check_sources, parse_checks


def invoke(command, text=None):
    result = subprocess.run(['timeout', '240', *command], cwd=ROOT, input=text,
                            capture_output=True, text=True, timeout=245)
    print(result.stdout, end='')
    print(result.stderr, end='', file=sys.stderr)
    if result.returncode == 124:
        raise subprocess.TimeoutExpired(command, 240, output=result.stdout, stderr=result.stderr)
    if result.returncode:
        raise RuntimeError(f'FAIL: command exited {result.returncode}')
    return result.stdout


def audit_axiom_output(output, declaration):
    records = re.findall(re.escape("'" + declaration + "'") +
                         r' depends on axioms:\s*\[([^]]*)\]', output)
    if not records and output.count("'" + declaration + "' does not depend on any axioms") == 1:
        records = ['']
    if len(records) != 1 or not {x.strip() for x in records[0].split(',') if x.strip()} <= ALLOWED:
        raise ValueError('Missing, ambiguous or disallowed axiom closure')


def audit_type_output(output, item):
    types = parse_checks(output, [item['declaration']])
    if types[item['declaration']] != ' '.join(item['type'].split()):
        raise ValueError('Declaration type differs from its registered statement')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source')
    parser.add_argument('declaration')
    args = parser.parse_args()
    check_sources()
    entries = json.loads((ROOT / 'scripts/headline-theorems.json').read_text())
    matches = [item for item in entries if item['module'] + '.lean' == args.source
               and item['declaration'] == args.declaration]
    if len(matches) != 1:
        raise ValueError('Unregistered source/declaration; no verification performed')
    item = matches[0]
    if not item.get('type'):
        raise ValueError('Exact declaration type has not been registered')
    invoke(['lake', 'build', item['module']])
    output = invoke(['lake', 'env', 'lean', '--stdin'],
                    f"import {item['module']}\n#print axioms {item['declaration']}\n")
    audit_axiom_output(output, item['declaration'])
    printed = invoke(['lake', 'env', 'lean', '--stdin'],
                     f"import {item['module']}\n#check @{item['declaration']}\n")
    audit_type_output(printed, item)
    print('RESULT: PASS')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except subprocess.TimeoutExpired:
        print('RESULT: UNKNOWN (timeout)', file=sys.stderr)
        sys.exit(124)
    except (OSError, ValueError, RuntimeError) as error:
        print('RESULT: FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
