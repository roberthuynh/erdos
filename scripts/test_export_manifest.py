#!/usr/bin/env python3
"""Exercise the public export boundary without Lean or a live project build."""
import json
from pathlib import Path
import tempfile
import unittest

from export_manifest import export_files


class ExportPolicyChecks(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='public-export-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.write('README.md', 'public\n')
        self.write('src/Main.lean', 'theorem sample : True := by trivial\n')
        self.policy = {'schema_version': 1, 'allowed_files': ['README.md', 'src/Main.lean'],
                       'required_files': ['README.md', 'src/Main.lean'], 'excluded_files': []}

    def write(self, relative, text='fixture'):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def exported(self):
        return [p.relative_to(self.root).as_posix() for p in export_files(self.root, policy=self.policy)]

    def test_exact_approved_files(self):
        self.assertEqual(self.exported(), ['README.md', 'src/Main.lean'])

    def test_real_export_requires_policy(self):
        with self.assertRaisesRegex(ValueError, 'policy required'):
            export_files(self.root)

    def test_default_policy_file(self):
        self.policy['allowed_files'].append('public-export-policy.json')
        self.write('public-export-policy.json', json.dumps(self.policy))
        self.assertIn('public-export-policy.json', [p.name for p in export_files(self.root)])

    def test_private_report_and_secret_additions_fail(self):
        for relative in ['private/notes.md', 'reports/review.json', '.env', 'src/secret.txt']:
            with self.subTest(path=relative):
                path = self.write(relative)
                with self.assertRaisesRegex(ValueError, 'Unapproved export'):
                    self.exported()
                path.unlink()
                if path.parent != self.root and not any(path.parent.iterdir()):
                    path.parent.rmdir()

    def test_unapproved_empty_directory_fails(self):
        (self.root / 'private').mkdir()
        with self.assertRaisesRegex(ValueError, 'Unapproved export directory'):
            self.exported()

    def test_source_and_external_symlinks_fail(self):
        for target in [self.root / 'README.md', Path('/etc/hosts')]:
            with self.subTest(target=target):
                link = self.root / 'src/linked.md'
                link.symlink_to(target)
                with self.assertRaisesRegex(ValueError, 'Symlink'):
                    self.exported()
                link.unlink()

    def test_directory_and_broken_symlinks_fail(self):
        for target in [self.root / 'src', self.root / 'absent']:
            with self.subTest(target=target):
                link = self.root / 'linked'
                link.symlink_to(target, target_is_directory=True)
                with self.assertRaisesRegex(ValueError, 'Symlink'):
                    self.exported()
                link.unlink()

    def test_symlink_cannot_hide_as_excluded_metadata_or_compiled_file(self):
        self.policy['excluded_files'].append('SOURCE-ENDPOINTS.json')
        for name in ['SOURCE-ENDPOINTS.json', 'hidden.pyc']:
            link = self.root / name
            link.symlink_to(self.root / 'README.md')
            with self.assertRaisesRegex(ValueError, 'Symlink'):
                self.exported()
            link.unlink()

    def test_runtime_and_compiled_files_excluded(self):
        for relative in ['.lake/build/Hidden.lean', '.git/config', 'scripts/__pycache__/x.pyc',
                         'runtime/secret.txt', 'cache/file', 'artifacts/check.json']:
            self.write(relative)
        # scripts is otherwise not an approved directory; runtime exclusion is at its own boundary.
        self.policy['allowed_files'].append('scripts/approved.py')
        for suffix in ['.pyc', '.pyo', '.olean', '.ilean', '.trace', '.o', '.so']:
            self.write('src/object' + suffix)
        self.assertEqual(self.exported(), ['README.md', 'src/Main.lean'])

    def test_explicit_internal_metadata_exclusion(self):
        self.policy['excluded_files'].append('SOURCE-ENDPOINTS.json')
        self.write('SOURCE-ENDPOINTS.json', 'private stale metadata')
        self.assertNotIn('SOURCE-ENDPOINTS.json', self.exported())

    def test_missing_required_legacy_file_fails(self):
        (self.root / 'README.md').unlink()
        with self.assertRaisesRegex(ValueError, 'Required public files missing'):
            self.exported()

    def test_output_exception_is_exact(self):
        output = self.write('manifest.json')
        files = export_files(self.root, exclude=output, policy=self.policy)
        self.assertEqual(len(files), 2)
        self.write('another-private.json')
        with self.assertRaisesRegex(ValueError, 'Unapproved export'):
            export_files(self.root, exclude=output, policy=self.policy)

    def test_invalid_and_runtime_policy_paths_rejected(self):
        for bad in ['/tmp/secret', '../secret', 'src/../secret', './README.md', 'a//b',
                    'a\\b', 'a*', '.lake/cache', 'object.olean', 'C:/secret']:
            with self.subTest(path=bad):
                policy = {**self.policy, 'allowed_files': self.policy['allowed_files'] + [bad]}
                with self.assertRaises(ValueError):
                    export_files(self.root, policy=policy)

    def test_duplicate_overlapping_and_unapproved_required_paths_rejected(self):
        for updates in [{'allowed_files': ['README.md', 'README.md']},
                        {'excluded_files': ['README.md']},
                        {'required_files': ['unapproved.md']}, {'schema_version': 2}]:
            with self.subTest(updates=updates):
                with self.assertRaises(ValueError):
                    export_files(self.root, policy={**self.policy, **updates})

    def test_private_paths_in_new_or_changed_files_fail(self):
        for text in ['reports/' + '585-fixture/receipt.json', '/' + 'Users/someone/private/file']:
            with self.subTest(text=text):
                self.write('README.md', text)
                with self.assertRaisesRegex(ValueError, 'Private source path'):
                    self.exported()

    def test_unchanged_public_blob_exempt_but_modification_scanned(self):
        import hashlib
        text = ('reports/' + '585-fixture/historical.log').encode()
        self.write('README.md', text.decode())
        identity = hashlib.sha1(f'blob {len(text)}\0'.encode() + text).hexdigest()
        self.policy['public_baseline_blobs'] = {'README.md': identity}
        self.assertIn('README.md', self.exported())
        self.write('README.md', text.decode() + '\nchanged')
        with self.assertRaisesRegex(ValueError, 'Private source path'):
            self.exported()

    def test_only_explicit_fixture_exemption_skips_content_scan(self):
        self.write('README.md', 'reports/' + '585-fixture/fixture.json')
        self.policy['content_scan_exemptions'] = ['README.md']
        self.assertIn('README.md', self.exported())
        self.policy['content_scan_exemptions'] = ['unapproved.md']
        with self.assertRaisesRegex(ValueError, 'Fixture exemptions'):
            self.exported()

    def test_private_marker_spanning_stream_boundary_rejected(self):
        self.write('README.md', 'x' * (1024 * 1024 - 3) + 'reports/' + '585-fixture/hidden.json')
        with self.assertRaisesRegex(ValueError, 'Private source path'):
            self.exported()

    def test_policy_symlink_rejected(self):
        (self.root / 'public-export-policy.json').symlink_to(self.root / 'README.md')
        with self.assertRaisesRegex(ValueError, 'policy must not be a symlink'):
            export_files(self.root)


if __name__ == '__main__':
    unittest.main()
