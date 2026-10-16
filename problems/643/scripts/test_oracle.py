#!/usr/bin/env python3
"""Negative controls: failed probe and foreign axiom must never pass."""
import contextlib,io,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import oracle
class OracleControls(unittest.TestCase):
 def probe(self,returncode,output):
  with tempfile.TemporaryDirectory() as d:
   root=Path(d);(root/'M.lean').write_text('theorem t : True := by trivial\n')
   (root/'source-identity.json').write_text(json.dumps({'root_module':'M','declaration':'t'}))
   from subprocess import CompletedProcess
   calls=[CompletedProcess([],0,'',''),CompletedProcess([],returncode,output,'')]
   with patch.object(oracle,'ROOT',root),patch('sys.argv',['oracle.py']),patch.object(oracle.subprocess,'run',side_effect=calls),contextlib.redirect_stdout(io.StringIO()):
    return oracle.main()
 def test_failed_probe(self):
  self.assertEqual(self.probe(1,"'t' depends on axioms: [propext]\n"),1)
 def test_disallowed_axiom(self):
  with self.assertRaisesRegex(ValueError,'disallowed axioms'):
   self.probe(0,"'t' depends on axioms: [propext, injectedAxiom]\n")
 def test_missing_probe(self):
  with self.assertRaisesRegex(ValueError,'missing'):
   self.probe(0,'')
if __name__=='__main__':unittest.main()
