#!/usr/bin/env python3
"""Check module build plans without executing Lean or changing proof sources."""
from pathlib import Path
import tempfile
import unittest
from check import build_order

class PlanTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name, source in {'Shared': '', 'Left': 'import Shared', 'Right': 'import Shared'}.items():
            (self.root / (name + '.lean')).write_text(source + '\n')
        self.lake('roots = ["Left", "Right"]')
    def lake(self, roots):
        (self.root / 'lakefile.toml').write_text('name = "fixture"\n[[lean_lib]]\nname = "Library"\n' + roots + '\n')
    def test_multiple_explicit_roots_build_shared_dependency_once(self):
        self.assertEqual(build_order(self.root, ['Right', 'Shared', 'Left'], 'Library'), ['Shared', 'Left', 'Right'])
    def test_leaf_before_parent_for_each_root(self):
        (self.root/'Right.lean').write_text('import Left\n')
        self.assertEqual(build_order(self.root, ['Right','Left','Shared'], 'Library'), ['Shared','Left','Right'])
    def test_all_configured_sources_remain_required(self):
        (self.root/'Extra.lean').write_text('')
        with self.assertRaisesRegex(ValueError, 'outside'):
            build_order(self.root, ['Left','Right','Shared','Extra'], 'Library')
    def test_missing_import_is_rejected(self):
        (self.root/'Shared.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing'):
            build_order(self.root, ['Left','Right','Shared'], 'Library')
    def test_unconfigured_local_import_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Unconfigured local import'):
            build_order(self.root, ['Left','Right'], 'Library')
    def test_missing_library_root_is_rejected(self):
        self.lake('roots = ["Missing"]')
        with self.assertRaisesRegex(ValueError, 'roots'):
            build_order(self.root, ['Left','Right','Shared'], 'Library')
    def test_duplicate_roots_are_rejected(self):
        self.lake('roots = ["Left", "Left"]')
        with self.assertRaisesRegex(ValueError, 'roots'):
            build_order(self.root, ['Left','Shared'], 'Library')
    def test_no_roots_does_not_guess(self):
        self.lake('')
        with self.assertRaisesRegex(ValueError, 'roots'):
            build_order(self.root, ['Left','Right','Shared'], 'Library')
    def test_duplicate_library_is_rejected(self):
        p=self.root/'lakefile.toml';p.write_text(p.read_text()+'\n[[lean_lib]]\nname = "Library"\nroots=["Left"]\n')
        with self.assertRaisesRegex(ValueError, 'unique'):
            build_order(self.root, ['Left','Right','Shared'], 'Library')
    def test_cycles_still_fail(self):
        (self.root/'Shared.lean').write_text('import Right\n')
        with self.assertRaisesRegex(ValueError, 'Cycle'):
            build_order(self.root, ['Left','Right','Shared'], 'Library')
    def test_existing_aggregate_order_is_preserved(self):
        (self.root/'Root.lean').write_text('import Left Right\n')
        self.assertEqual(build_order(self.root, ['Right','Root','Left','Shared'], 'Root'), ['Shared','Left','Right','Root'])

if __name__ == '__main__':
    unittest.main()
