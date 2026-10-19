"""Filesystem controls for both artifact pin verifiers; no Lean invocation."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parent


class ArtifactPinControls(unittest.TestCase):
    def exercise(self, script, mutation):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            tools = root / 'tools'
            tools.mkdir()
            shutil.copyfile(TOOLS / script, tools / script)
            (root / 'standalone').mkdir()
            (root / 'standalone/lake-manifest.json').write_text(
                json.dumps({'packages': [{'name': 'pkg'}, {'name': 'unbuilt'}]}))
            tree = root / 'artifacts'
            if script == 'toolchain_pins.py':
                base = tree / 'lib/lean'
                (tree / 'bin').mkdir(parents=True)
                (tree / 'bin/lean').write_bytes(b'compiler fixture')
            else:
                base = tree / 'pkg/.lake/build/lib/lean'
            base.mkdir(parents=True)
            subtree = base / 'Expected'
            subtree.mkdir()
            artifact = subtree / 'Foo.olean'
            artifact.write_bytes(b'expected module fixture')
            pins = root / 'pins'

            def run(mode):
                return subprocess.run(
                    [sys.executable, '-I', str(tools / script), mode, str(tree), str(pins)],
                    capture_output=True, text=True, timeout=10)

            self.assertEqual(run('make').returncode, 0)
            before = pins.read_bytes()
            self.assertEqual(run('verify').returncode, 0)
            external = root / 'external'
            external.mkdir()
            (external / 'Foo.olean').write_bytes(artifact.read_bytes())
            if mutation == 'allowed':
                self.assertEqual(run('verify').returncode, 0)
                return
            if mutation == 'extra-directory-link':
                (base / 'Extra').symlink_to(external, target_is_directory=True)
            elif mutation == 'replacement-directory-link':
                shutil.rmtree(subtree)
                subtree.symlink_to(external, target_is_directory=True)
            elif mutation == 'dangling-directory-link':
                (base / 'Missing').symlink_to(root / 'absent', target_is_directory=True)
            elif mutation == 'root-directory-link':
                moved = root / 'moved'
                tree.rename(moved)
                tree.symlink_to(moved, target_is_directory=True)
            elif mutation == 'base-directory-link':
                moved = root / 'moved'
                base.rename(moved)
                base.symlink_to(moved, target_is_directory=True)
            elif mutation == 'ancestor-directory-link':
                ancestor = base.parent
                moved = root / 'moved'
                ancestor.rename(moved)
                ancestor.symlink_to(moved, target_is_directory=True)
            elif mutation == 'replacement-file-link':
                artifact.unlink()
                artifact.symlink_to(external / 'Foo.olean')
            elif mutation == 'extra-file-link':
                (base / 'Extra.olean').symlink_to(external / 'Foo.olean')
            elif mutation == 'dangling-file-link':
                (base / 'Missing.olean').symlink_to(root / 'absent-file')
            elif mutation == 'extra-file':
                (base / 'Extra.olean').write_bytes(b'extra artifact')
            elif mutation == 'changed-file':
                artifact.write_bytes(b'changed artifact')
            elif mutation == 'missing-file':
                artifact.unlink()
            else:
                self.fail('unknown mutation')
            result = run('verify')
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            if mutation.endswith('link'):
                self.assertIn('symbolic link', result.stderr)
                self.assertNotEqual(run('make').returncode, 0)
                self.assertEqual(pins.read_bytes(), before)

    def test_inventories(self):
        for script in ('toolchain_pins.py', 'olean_pins.py'):
            for mutation in (
                'allowed', 'extra-directory-link', 'replacement-directory-link',
                'dangling-directory-link', 'root-directory-link', 'base-directory-link', 'ancestor-directory-link',
                'replacement-file-link', 'extra-file-link', 'dangling-file-link',
                'extra-file', 'changed-file', 'missing-file',
            ):
                with self.subTest(script=script, mutation=mutation):
                    self.exercise(script, mutation)


if __name__ == '__main__':
    unittest.main(verbosity=2)
