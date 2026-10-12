#!/usr/bin/env python3
"""Register pending headline types from captured successful Lean #check output."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

from check_axioms import parse_checks

ROOT = Path(__file__).resolve().parent.parent


def pending_entries(entries):
    return [entry for entry in entries if entry.get('registration_status') == 'pending_exact_type']


def query(entries):
    return ''.join(f'import {module}\n' for module in sorted({e['module'] for e in entries})) + \
        '\n/-! Exact headline type registration. -/\n' + ''.join(f'#check @{e["declaration"]}\n' for e in entries)


def register(entries, output, root=ROOT):
    pending = pending_entries(entries)
    if not pending:
        raise ValueError('No pending headline types')
    if any(token in output for token in ('error:', 'warning:', 'sorryAx')):
        raise ValueError('Lean output contains diagnostics or sorryAx')
    types = parse_checks(output, [e['declaration'] for e in pending])
    output_sha = hashlib.sha256(output.encode()).hexdigest()
    query_sha = hashlib.sha256(query(pending).encode()).hexdigest()
    for entry in pending:
        printed = types[entry['declaration']]
        if not printed:
            raise ValueError(f'Empty printed type: {entry["declaration"]}')
        source = root / (entry['module'].replace('.', '/') + '.lean')
        if hashlib.sha256(source.read_bytes()).hexdigest() != entry['source_sha256']:
            raise ValueError(f'Source changed before registration: {entry["module"]}')
        entry['type'] = printed
        entry['registration_status'] = 'exact_printed_type'
        entry['type_evidence'] = {'method': 'successful lake env lean --stdin; #check @declaration',
                                  'query_sha256': query_sha, 'output_sha256': output_sha,
                                  'toolchain_sha256': hashlib.sha256((root / 'lean-toolchain').read_bytes()).hexdigest()}
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--emit-query', action='store_true')
    group.add_argument('--register-output', type=Path)
    parser.add_argument('--lean-exit-code', type=int, help='Required successful capture exit code for registration')
    args = parser.parse_args()
    registry = ROOT / 'scripts/headline-theorems.json'
    entries = json.loads(registry.read_text())
    if args.emit_query:
        sys.stdout.write(query(pending_entries(entries)))
    else:
        if args.lean_exit_code != 0:
            parser.error('--register-output requires --lean-exit-code 0 from the captured Lean command')
        register(entries, args.register_output.read_text())
        registry.write_text(json.dumps(entries, indent=2, ensure_ascii=False) + '\n')
        print('Registered exact printed types; run scripts/check_axioms.py to independently recheck them.')


if __name__ == '__main__':
    main()
