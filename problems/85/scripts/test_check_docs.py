#!/usr/bin/env python3
"""Negative controls for the package identity checker."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from check_docs import ROOT, check, safe_manifest_file

class NegativeControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        collection = Path(self.tmp.name)/'collection'
        self.root = collection/'problems/85'
        shutil.copytree(ROOT,self.root,ignore=shutil.ignore_patterns('__pycache__', '.lake'))
        for name in ['README.md','CONTRIBUTING.md']:
            shutil.copyfile(ROOT.parents[1]/name,collection/name)
    def rehash(self, name):
        path = self.root/name
        manifest = self.root/'document-hashes.json'
        data = json.loads(manifest.read_text())
        data[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        manifest.write_text(json.dumps(data))
    def test_clean(self):
        with contextlib.redirect_stdout(io.StringIO()): check(self.root)
    def test_changed_document(self):
        with (self.root/'PROOF.md').open('a') as f: f.write('\nchanged\n')
        with self.assertRaisesRegex(ValueError,'identity'): check(self.root)
    def test_unlisted_file(self):
        (self.root/'extra.txt').write_text('unreviewed')
        with self.assertRaisesRegex(ValueError,'Unlisted'): check(self.root)
    def test_broken_link_even_if_rehashed(self):
        path=self.root/'README.md';path.write_text(path.read_text()+'\n[bad](missing.md)\n')
        self.rehash('README.md')
        with self.assertRaisesRegex(ValueError,'Broken/escaping local link'): check(self.root)
    def test_existing_file_outside_collection_is_rejected(self):
        outside = Path(self.tmp.name)/'outside.md'
        outside.write_text('# Existing outside file\n')
        path = self.root/'README.md'
        path.write_text(path.read_text()+'\n[outside](../../../outside.md)\n')
        self.rehash('README.md')
        with self.assertRaisesRegex(ValueError,'Broken/escaping local link'): check(self.root)
    def test_fragment_only_and_duplicate_heading(self):
        path = self.root/'README.md'
        path.write_text(path.read_text()+'\n## Repeated\n## Repeated\n[second](#repeated-1)\n')
        self.rehash('README.md')
        with contextlib.redirect_stdout(io.StringIO()): check(self.root)
    def test_fenced_heading_is_not_a_fragment(self):
        path = self.root/'README.md'
        path.write_text(path.read_text()+'\n```md\n## Fake heading\n```\n[bad](#fake-heading)\n')
        self.rehash('README.md')
        with self.assertRaisesRegex(ValueError,'Broken local fragment'): check(self.root)
    def test_broken_symlink_is_rejected(self):
        (self.root/'broken.txt').symlink_to('missing-target.txt')
        with self.assertRaisesRegex(ValueError,'Symlink'): check(self.root)
    def test_manifest_symlink_ancestor_is_rejected(self):
        (self.root/'alias').symlink_to(self.root/'scripts', target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'Missing/unsafe document'):
            safe_manifest_file(self.root, 'alias/check_docs.py')
    def test_unsafe_manifest_path_is_rejected(self):
        manifest = self.root/'document-hashes.json'
        data = json.loads(manifest.read_text())
        data['../outside.md'] = '0'*64
        manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError,'Unsafe manifest path'): check(self.root)

if __name__ == '__main__': unittest.main()
