#!/usr/bin/env python3
"""Negative controls for graph/certificate validation, including optimized Python."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
CERT = ROOT / 'findings/supplement/small-values/certificates'


class ValidationModes(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='validation-modes-')
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)
        self.env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
        self.env.pop('PYTHONOPTIMIZE', None)

    def run_python(self, source, optimized=None):
        args = [sys.executable, '-B']
        env = dict(self.env)
        if optimized == 'flag':
            args.append('-O')
        if optimized == 'environment':
            env['PYTHONOPTIMIZE'] = '1'
        args.append(source)
        return subprocess.run(args, cwd=self.work, env=env, capture_output=True,
                              text=True, timeout=30)

    def test_all_entrypoints_reject_both_optimization_modes(self):
        for source in [ROOT / 'graphs/verify_graphs.py', CERT / 'verify_certificates.py',
                       CERT / 'verify_full_streams.py']:
            shutil.copy2(source, self.work / source.name)
            for mode in ['flag', 'environment']:
                with self.subTest(entrypoint=source.name, mode=mode):
                    run = self.run_python(source.name, mode)
                    self.assertNotEqual(run.returncode, 0)
                    self.assertIn('optimization', run.stderr)
                    self.assertNotIn('all checks passed', run.stdout)
                    self.assertFalse(list(self.work.rglob('*verified*.json')))
                    self.assertFalse(list(self.work.rglob('*verification*.json')))

    def test_missing_graph_inputs_rejected_without_success(self):
        shutil.copy2(ROOT / 'graphs/verify_graphs.py', self.work / 'verify_graphs.py')
        run = self.run_python('verify_graphs.py')
        self.assertNotEqual(run.returncode, 0)
        self.assertNotIn('all checks passed', run.stdout)

    def test_cycle_without_graph_edges_rejected(self):
        shutil.copy2(CERT / 'verify_certificates.py', self.work / 'verify_certificates.py')
        (self.work / 'invalid.py').write_text(
            'from verify_certificates import cycle_vertices\n'
            'cycle_vertices("0,1,2,3,4", 5, set())\n')
        run = self.run_python('invalid.py')
        self.assertNotEqual(run.returncode, 0)
        self.assertIn('AssertionError', run.stderr)

    def test_inconsistent_empty_stream_receipts_rejected(self):
        import json
        for name in ['verify_certificates.py', 'verify_full_streams.py']:
            shutil.copy2(CERT / name, self.work / name)
        (self.work / 'data').mkdir()
        (self.work / 'receipts').mkdir()
        for count in [1, 0]:
            with self.subTest(count=count):
                for label in ['parent-n10-e26', 'parent-n10-e27', 'baseline-n10-e28']:
                    for suffix in ['.all.g6', '.cycles.tsv', '.free.g6']:
                        (self.work / 'data' / (label + suffix)).write_text('')
                    (self.work / 'receipts' / (label + '.json')).write_text(json.dumps({
                        'complete': True, 'generated': count, 'all_graphs_lines': count,
                        'cycle_certificate_lines': count, 'free_catalogue_lines': count,
                        'all_graphs_sha256': 'wrong', 'cycle_certificates_sha256': 'wrong',
                        'free_catalogue_sha256': 'wrong'}))
                run = self.run_python('verify_full_streams.py')
                self.assertNotEqual(run.returncode, 0)
                self.assertFalse((self.work / 'receipts/full-stream-certificate-verification.json').exists())
                self.assertFalse(list((self.work / 'receipts').glob('*.certificate-verified.json')))


if __name__ == '__main__':
    unittest.main()
