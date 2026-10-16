#!/usr/bin/env python3
"""Exercise multi-root coverage, proof scanning and exact type registration without Lean."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from check_axioms import ROOT, STATEMENT_SHA256, check_sources, lean_code
from export_manifest import export_files
from register_headlines import query, register
from source_modules import check_coverage


class ReleaseChecks(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='release-checks-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for d in ['Openmath', 'Extra']:
            (self.root / d).mkdir()
        (self.root / 'lakefile.toml').write_text('[[lean_lib]]\nname="Openmath"\n\n[[lean_lib]]\nname="Extra"\nglobs=["Extra.+"]\n\n[[lean_lib]]\nname="Single"\nglobs=["Single"]\n')
        (self.root / 'Openmath.lean').write_text('import Openmath.Target\nimport Extra.Main\nimport Single\n')
        shutil.copy2(ROOT / 'Openmath/Target.lean', self.root / 'Openmath/Target.lean')
        (self.root / 'Extra/Main.lean').write_text('import Extra.Support\ntheorem sample : True := by trivial\n')
        (self.root / 'Extra/Support.lean').write_text('theorem support : True := by trivial\n')
        (self.root / 'Single.lean').write_text('theorem singleton : True := by trivial\n')
        (self.root / 'Axioms.lean').write_text('import Extra.Main\n')
        (self.root / 'lean-toolchain').write_text('fixture-only\n')

    def test_transitive_multiroot_and_singleton_coverage(self):
        self.assertEqual(set(check_coverage(self.root)), {'Openmath', 'Openmath.Target', 'Extra.Main', 'Extra.Support', 'Single'})
        self.assertEqual(check_sources(self.root), 6)

    def test_unreachable_custom_module_rejected(self):
        (self.root / 'Extra/Orphan.lean').write_text('theorem orphan : True := by trivial\n')
        with self.assertRaisesRegex(ValueError, 'outside transitive'):
            check_coverage(self.root)

    def test_disallowed_proof_in_non_openmath_root_rejected(self):
        (self.root / 'Extra/Support.lean').write_text('theorem support : True := by native_decide\n')
        with self.assertRaisesRegex(ValueError, 'Extra/Support.lean'):
            check_sources(self.root)

    def test_executable_interpolations_rejected(self):
        for prefix in ['s!', 'm!', 'f!', 'custom!', 's! /- comment -/ ']:
            for token in ['sorry', 'admit', 'native_decide']:
                with self.subTest(prefix=prefix, token=token):
                    (self.root / 'Extra/Support.lean').write_text(
                        'def hidden := ' + prefix + '"{(by ' + token + ' : Nat)}"\n')
                    with self.assertRaisesRegex(ValueError, 'Interpolated strings'):
                        check_sources(self.root)

    def test_plain_strings_and_interpolation_inside_comments_allowed(self):
        self.assertEqual(lean_code('def message := "s! sorry \\\"admit\\\""'), 'def message :=  ')
        self.assertEqual(' '.join(lean_code(
            '/- s!"{sorry}" /- nested -/ -/ theorem ok : True := by trivial').split()),
            'theorem ok : True := by trivial')

    def test_frozen_target_remains_only_source_exception(self):
        self.assertEqual(hashlib.sha256((self.root / 'Openmath/Target.lean').read_bytes()).hexdigest(), STATEMENT_SHA256)
        with (self.root / 'Openmath/Target.lean').open('a') as f:
            f.write('\n')
        with self.assertRaisesRegex(ValueError, 'frozen submitted'):
            check_sources(self.root)

    def test_export_excludes_runtime_and_python_caches(self):
        for path in ['.lake/build/Hidden.lean', 'scripts/__pycache__/module.pyc', 'loose.pyc']:
            p = self.root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('excluded')
        exported = {p.relative_to(self.root).as_posix() for p in export_files(self.root, policy={
            'schema_version': 1,
            'allowed_files': ['lakefile.toml', 'Openmath.lean', 'Openmath/Target.lean',
                              'Extra/Main.lean', 'Extra/Support.lean', 'Single.lean',
                              'Axioms.lean', 'lean-toolchain', 'scripts/export_manifest.py'],
            'excluded_files': [],
        })}
        self.assertFalse(any('.lake' in p or '__pycache__' in p or p.endswith('.pyc') for p in exported))

    def fixture_entries(self):
        return [{'module': 'Extra.Main', 'declaration': 'Fixture.sample', 'type': None,
                 'registration_status': 'pending_exact_type',
                 'source_sha256': hashlib.sha256((self.root / 'Extra/Main.lean').read_bytes()).hexdigest()}]

    def test_registration_uses_exact_printed_type(self):
        entries = self.fixture_entries()
        self.assertEqual(query(entries), 'import Extra.Main\n\n/-! Exact headline type registration. -/\n#check @Fixture.sample\n')
        result = register(entries, '@Fixture.sample : ∀ (n : Nat),\n  n = n\n', self.root)
        self.assertEqual(result[0]['type'], '∀ (n : Nat), n = n')
        self.assertEqual(result[0]['registration_status'], 'exact_printed_type')

    def test_registration_rejects_diagnostics_missing_duplicate_or_changed_source(self):
        for output in ['error: failure\n', '@Wrong.name : True\n', '@Fixture.sample : True\n@Fixture.sample : True\n']:
            with self.assertRaises(ValueError):
                register(self.fixture_entries(), output, self.root)
        entries = self.fixture_entries()
        (self.root / 'Extra/Main.lean').write_text('changed source\n')
        with self.assertRaisesRegex(ValueError, 'Source changed'):
            register(entries, '@Fixture.sample : True\n', self.root)

    def test_candidate_driver_matches_registry(self):
        entries = json.loads((ROOT / 'scripts/headline-theorems.json').read_text())
        import re
        printed = re.findall(r'^#print axioms (\S+)$', (ROOT / 'Axioms.lean').read_text(), re.M)
        self.assertEqual(len(entries), len(printed))
        self.assertEqual({e['declaration'] for e in entries}, set(printed))


if __name__ == '__main__':
    unittest.main()
