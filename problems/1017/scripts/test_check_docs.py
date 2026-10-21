#!/usr/bin/env python3
"""Regression checks for frozen identities and local-link boundaries."""
import contextlib,hashlib,io,json,shutil,tempfile,unittest
from pathlib import Path
from check_docs import ROOT,check,headings
class DocsTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
  self.root=Path(self.tmp.name)/'problems'/'test';self.root.mkdir(parents=True)
  (self.root/'Erdos1017').mkdir();(self.root/'Erdos1017/Test.lean').write_text('theorem test : True := True.intro\n')
  (self.root/'README.md').write_text('# Test\n\n[Result](RESULTS.md#claim)\n')
  (self.root/'RESULTS.md').write_text('# Claim\n')
  self.freeze()
 def freeze(self):
  sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
  data={'project_sources':{'Erdos1017.Test':{'path':'Erdos1017/Test.lean','sha256':sha(self.root/'Erdos1017/Test.lean')}},'artifact_hashes':{f.name:sha(f) for f in self.root.glob('*.md')}}
  (self.root/'source-identity.json').write_text(json.dumps(data))
 def run_check(self):
  with contextlib.redirect_stdout(io.StringIO()):check(self.root)
 def test_baseline(self):self.run_check()
 def test_changed_source(self):
  (self.root/'Erdos1017/Test.lean').write_text('theorem test : True := by trivial\n')
  with self.assertRaisesRegex(ValueError,'Source hash'):self.run_check()
 def test_changed_doc(self):
  (self.root/'README.md').write_text('# Changed\n')
  with self.assertRaisesRegex(ValueError,'Artifact hash'):self.run_check()
 def test_added_source(self):
  (self.root/'Erdos1017/Extra.lean').write_text('')
  with self.assertRaisesRegex(ValueError,'closure'):self.run_check()
 def test_unregistered_doc(self):
  (self.root/'EXTRA.md').write_text('extra')
  with self.assertRaisesRegex(ValueError,'Unregistered'):self.run_check()
 def test_broken_link(self):
  (self.root/'README.md').write_text('[Missing](MISSING.md)');self.freeze()
  with self.assertRaisesRegex(ValueError,'local link'):self.run_check()
 def test_broken_anchor(self):
  (self.root/'README.md').write_text('[Missing](RESULTS.md#missing)');self.freeze()
  with self.assertRaisesRegex(ValueError,'fragment'):self.run_check()
 def test_escaping_link(self):
  (self.root/'README.md').write_text('[External](../../../../etc/passwd)');self.freeze()
  with self.assertRaisesRegex(ValueError,'escaping'):self.run_check()
 def test_duplicate_headings_and_fences(self):
  self.assertEqual(headings('# A\n# A\n```\n# Hidden\n```\n'),{'a','a-1'})
if __name__=='__main__':unittest.main()
