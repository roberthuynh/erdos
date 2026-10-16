#!/usr/bin/env python3
"""Negative controls for stale release metadata and broken reproduction links."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from check_docs import check_docs


class DocumentationChecks(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='documentation-checks-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'scripts').mkdir()
        self.metadata = {'version': '0.4.1', 'date': '2026-10-14',
                         'repository': 'https://github.com/OWNER/REPO',
                         'verification_inventory': {'declarations': 1, 'oracles': 1, 'modules': 1}}
        (self.root / 'scripts/release-metadata.json').write_text(json.dumps(self.metadata))
        (self.root / 'scripts/headline-theorems.json').write_text(json.dumps([{'oracle': True}]))
        (self.root / 'CITATION.cff').write_text('version: "0.4.1"\ndate-released: "2026-10-14"\n'
            'repository-code: "https://github.com/OWNER/REPO"\n')
        (self.root / 'README.md').write_text('Current verification inventory: 1 registered declarations, '
            '1 whole-file oracle checks, 1 configured custom modules.\n[Source](proof.lean)\n')
        (self.root / 'proof.lean').write_text('theorem sample : True := by trivial\n')
        self.coverage = patch('check_docs.check_coverage', return_value={'Proof': None})
        self.coverage.start()
        self.addCleanup(self.coverage.stop)

    def test_consistent_inventory_and_link_pass(self):
        self.assertEqual(check_docs(self.root, ['README.md'])[1], 1)

    def test_missing_local_source_rejected(self):
        (self.root / 'proof.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Invalid local link'):
            check_docs(self.root, ['README.md'])

    def test_stale_inventory_rejected(self):
        self.metadata['verification_inventory']['declarations'] = 2
        (self.root / 'scripts/release-metadata.json').write_text(json.dumps(self.metadata))
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            check_docs(self.root, ['README.md'])

    def test_stale_citation_rejected(self):
        (self.root / 'CITATION.cff').write_text('version: "0.4"\n')
        with self.assertRaisesRegex(ValueError, 'Citation version'):
            check_docs(self.root, ['README.md'])


if __name__ == '__main__':
    unittest.main()
