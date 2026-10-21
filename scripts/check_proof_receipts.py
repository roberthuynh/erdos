#!/usr/bin/env python3
"""Check published mathematical input bindings without rerunning Lean.

This check does not authenticate evidence provenance or establish a new proof
PASS. The release publisher authenticates accepted evidence before export.
"""
import argparse
import json
from pathlib import Path
import re
import sys
from check import ROOT, load_registry
from mathematical_inputs import POLICY, digest, project, phased_project, read, lean_code

RECEIPT = 'verification/accepted-mathematical-inputs.json'
COLLECTION_INPUTS = {'scripts/check.py', 'scripts/mathematical_inputs.py', 'scripts/check_proof_receipts.py'}
HEX = re.compile(r'[0-9a-f]{64}')


def unique_strings(values, label):
    if (not isinstance(values, list) or not all(isinstance(v, str) and v for v in values)
            or len(values) != len(set(values))):
        raise ValueError('Invalid or duplicate ' + label)
    return set(values)


def check_receipt(root, item):
    if 'lean' not in item:
        raise ValueError('Mathematical receipt requires a registered Lean package')
    package = Path(root) / item['path']
    raw = read(package, RECEIPT)
    receipt = json.loads(raw)
    if (not isinstance(receipt, dict) or set(receipt) != {'schema', 'policy', 'problem', 'main', 'phased', 'evidence', 'collection_inputs'}
            or type(receipt['schema']) is not int or receipt['schema'] != 1
            or receipt['policy'] != POLICY or receipt['problem'] != item['id']):
        raise ValueError('Invalid mathematical receipt envelope')
    if receipt['collection_inputs'] != {path: digest(read(root, path)) for path in sorted(COLLECTION_INPUTS)}:
        raise ValueError('Current collection checkers differ from the published binding')
    main = receipt['main']
    if not isinstance(main, dict) or set(main) != {'projection', 'mathematical_input_sha256', 'raw_sources'}:
        raise ValueError('Invalid main project binding')
    declarations = main.get('projection', {}).get('declarations')
    if not isinstance(declarations, list) or not declarations:
        raise ValueError('Missing main declaration coverage')
    accepted_axioms = {}
    for row in declarations:
        if not isinstance(row, dict) or not isinstance(row.get('name'), str) or row['name'] in accepted_axioms:
            raise ValueError('Invalid or duplicate bound declaration')
        accepted_axioms[row['name']] = row.get('axioms')
    actual = project(package, item['lean'], accepted_axioms=accepted_axioms)
    if actual != main:
        raise ValueError('Current mathematical inputs differ from the published binding')
    modules = set(actual['projection']['coverage']['modules'])
    names = {row['name'] for row in actual['projection']['declarations']}
    evidence = receipt['evidence']
    if not isinstance(evidence, list) or not evidence:
        raise ValueError('Missing accepted evidence description')
    covered_modules, covered_names = set(), set()
    structural = {}
    declaration_modules = {row['module'] for row in actual['projection']['declarations']}
    for row in evidence:
        if (not isinstance(row, dict) or set(row) != {'kind', 'receipt_sha256', 'acceptance_sha256', 'modules', 'declarations'}
                or row['kind'] not in {'historical-clean', 'owned-completed', 'structural-imports'}
                or not all(isinstance(row[key], str) and HEX.fullmatch(row[key]) for key in ['receipt_sha256', 'acceptance_sha256'])):
            raise ValueError('Invalid accepted evidence description')
        row_modules = unique_strings(row['modules'], 'evidence modules')
        row_names = unique_strings(row['declarations'], 'evidence declarations')
        if row['kind'] == 'structural-imports':
            if len(row_modules) != 1 or row_names or not row_modules <= modules:
                raise ValueError('Structural evidence requires one configured module and no declarations')
            module = next(iter(row_modules))
            if module in structural or module in declaration_modules:
                raise ValueError('Duplicate structural module or registered declarations in structural module')
            source = actual['raw_sources'][module]['path']
            if source != module.replace('.', '/') + '.lean':
                raise ValueError('Structural module source path differs from its configured name')
            raw_source = read(package, source)
            if digest(raw_source) != row['receipt_sha256']:
                raise ValueError('Structural source hash differs from its evidence')
            lines = lean_code(raw_source).decode().splitlines()
            if not lines or any(not re.fullmatch(r'import[ \t]+[A-Za-z_][A-Za-z_0-9.]*(?:[ \t]+[A-Za-z_][A-Za-z_0-9.]*)*', line.strip()) for line in lines):
                raise ValueError('Structural module must contain only import commands')
            structural[module] = {name for line in lines for name in line.split()[1:]}
            continue
        if not row_modules or not row_names or not row_modules <= modules or not row_names <= names:
            raise ValueError('Evidence describes missing or foreign coverage')
        covered_modules.update(row_modules); covered_names.update(row_names)
    for module, imports in structural.items():
        if module in covered_modules or not imports <= covered_modules:
            raise ValueError('Structural imports require distinct nonstructural accepted module coverage')
    covered_modules.update(structural)
    if covered_modules != modules or covered_names != names:
        raise ValueError('Accepted evidence does not cover every main module and declaration')
    phased = receipt['phased']
    expected_paths = [entry['path'] for entry in item.get('phased_lean', [])]
    if (not isinstance(phased, list) or len(expected_paths) != len(set(expected_paths))
            or any(not isinstance(entry, dict) or not isinstance(entry.get('path'), str) for entry in phased)
            or len(phased) != len(expected_paths) or {entry['path'] for entry in phased} != set(expected_paths)):
        raise ValueError('Missing, duplicate or extra phased project binding')
    for descriptor in phased:
        expected_configuration = next(entry for entry in item['phased_lean'] if entry['path'] == descriptor['path'])
        if descriptor.get('configuration') != expected_configuration:
            raise ValueError('Phased registry configuration differs from the published binding')
        if phased_project(package, descriptor) != descriptor:
            raise ValueError('Current phased mathematical inputs differ from the published binding')
    return {'problem': item['id'], 'status': 'MATCH', 'policy': POLICY,
            'receipt_sha256': digest(raw), 'mathematical_input_sha256': actual['mathematical_input_sha256'],
            'modules': len(modules), 'declarations': len(names), 'phased_projects': len(phased),
            'proof_executed': False, 'provenance_authenticated': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--problem', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    registry = load_registry()
    if args.problem not in registry:
        raise ValueError('Unknown problem ID')
    args.output.mkdir(parents=True, exist_ok=True)
    try:
        result = check_receipt(ROOT, registry[args.problem])
    except (ValueError, KeyError, TypeError, OSError) as error:
        (args.output / 'binding-check.json').write_text(json.dumps({
            'problem': args.problem, 'status': 'FAIL', 'error': str(error),
            'proof_executed': False, 'provenance_authenticated': False}, indent=2) + '\n')
        raise
    (args.output / 'binding-check.json').write_text(json.dumps(result, indent=2) + '\n')
    print('MATHEMATICAL INPUT BINDING: MATCH (' + args.problem + '; no proof execution or provenance authentication)')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as error:
        print('MATHEMATICAL INPUT BINDING: FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
