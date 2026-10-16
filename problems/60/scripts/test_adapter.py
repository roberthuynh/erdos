#!/usr/bin/env python3
"""Failure controls for the portable source, registry and replay adapter."""
import copy
import json
from pathlib import Path
import re
import sys
import tempfile
import subprocess
import unittest
from unittest.mock import patch
import check_axioms
import oracle
import replay_modules
import source_modules


class AdapterTests(unittest.TestCase):
    def test_exact_module_inventory(self):
        modules = source_modules.check_coverage()
        self.assertEqual(len(modules), 82)
        self.assertIn('Erdos60', modules)

    def test_frozen_sources(self):
        self.assertEqual(check_axioms.check_sources(), 83)

    def test_locked_dependency(self):
        manifest = json.loads((check_axioms.ROOT / 'lake-manifest.json').read_text())
        deps = {p['name']: p for p in manifest['packages']}
        self.assertEqual(deps['mathlib']['rev'], '0df444a360eaa60ab8c11dca51a86af692955474')
        self.assertNotIn('formal_conjectures', deps)
        self.assertEqual((check_axioms.ROOT / 'lean-toolchain').read_text().strip(), 'leanprover/lean4:v4.33.1')

    def test_comments_do_not_hide_proof_tokens(self):
        text = '/- outer /- nested -/ still comment -/ theorem x : True := by sorry'
        self.assertRegex(check_axioms.lean_code(text), check_axioms.DISALLOWED)

    def test_comment_and_string_tokens_ignored(self):
        self.assertNotRegex(check_axioms.lean_code('/- sorry -/ "axiom" -- native_decide\n'), check_axioms.DISALLOWED)

    def test_native_kernel_bypass_rejected(self):
        for token in ['native_decide', 'debug.skipKernelTC', 'unsafe', 'axiom', 'implemented_by', 'ofReduceBool']:
            self.assertRegex(check_axioms.lean_code(token), check_axioms.DISALLOWED)

    def test_interpolated_string_rejected(self):
        with self.assertRaises(ValueError):
            check_axioms.lean_code('s!"{anything}"')

    def test_unregistered_oracle_never_executes(self):
        with patch.object(sys, 'argv', ['oracle.py', 'Unknown.lean', 'Unknown.result']):
            with patch.object(oracle, 'invoke', side_effect=AssertionError('must not run')):
                with self.assertRaisesRegex(ValueError, 'Unregistered'):
                    oracle.main()

    def test_unconfigured_replay_never_executes(self):
        with self.assertRaisesRegex(ValueError, 'not configured'):
            replay_modules.replay(selected=['Unknown'], run=lambda *a, **k: self.fail('must not run'))

    def test_parse_checks_missing_type_fails(self):
        with self.assertRaisesRegex(ValueError, 'No #check'):
            check_axioms.parse_checks('', ['Example.result'])

    def test_parse_checks_duplicate_fails(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            check_axioms.parse_checks('Example.result : True\nExample.result : True\n', ['Example.result'])

    def test_type_mismatch_rejected(self):
        with self.assertRaisesRegex(ValueError, 'differs'):
            oracle.audit_type_output('Example.result : False\n', {'declaration': 'Example.result', 'type': 'True'})

    def test_disallowed_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, 'disallowed'):
            oracle.audit_axiom_output("'Example.result' depends on axioms: [sorryAx]", 'Example.result')

    def test_missing_axiom_record_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Missing'):
            oracle.audit_axiom_output('', 'Example.result')

    def test_source_hash_change_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            for module, path in source_modules.check_coverage().items():
                (root / path.name).write_bytes(path.read_bytes())
            (root / 'Axioms.lean').write_bytes((check_axioms.ROOT / 'Axioms.lean').read_bytes())
            for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
                (root / name).write_bytes((check_axioms.ROOT / name).read_bytes())
            for name in ['proof-modules.json', 'headline-theorems.json']:
                (root / 'scripts' / name).write_bytes((check_axioms.ROOT / 'scripts' / name).read_bytes())
            path = root / 'C4Counting.lean'
            path.write_text(path.read_text() + '\n-- changed bytes\n')
            with self.assertRaisesRegex(ValueError, 'Frozen proof source differs'):
                check_axioms.check_sources(root)

    def test_timeout_is_unknown(self):
        result = subprocess.CompletedProcess(['lake'], 124, stdout='timed out', stderr='')
        with patch.object(oracle.subprocess, 'run', return_value=result):
            with self.assertRaises(subprocess.TimeoutExpired):
                oracle.invoke(['lake', 'build', 'Erdos60'])

    def test_coverage_detects_unreachable_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lakefile.toml').write_text('[[lean_lib]]\nname="Erdos60"\nglobs=["Erdos60","Hidden"]\n')
            (root / 'Erdos60.lean').write_text('')
            (root / 'Hidden.lean').write_text('')
            with self.assertRaisesRegex(ValueError, 'outside transitive'):
                source_modules.check_coverage(root)


if __name__ == '__main__':
    unittest.main()
