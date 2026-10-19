"""Runner controls in disposable package copies; no full-domain checker executions."""
import hashlib,importlib.util,json,shutil,subprocess,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parent
class ReplayControls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='643-replay-control-')
        self.base=Path(self.temp.name);self.root=self.base/'package';shutil.copytree(ROOT,self.root,ignore=shutil.ignore_patterns('__pycache__'))
        spec=importlib.util.spec_from_file_location('fixture_replay',self.root/'replay.py');self.runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(self.runner)
        self.out=self.base/'output'
    def tearDown(self):self.temp.cleanup()
    def invoke(self,effect):
        with patch.object(sys,'argv',[str(self.root/'replay.py'),str(self.out)]),patch('subprocess.run',side_effect=effect):return self.runner.main()
    def failed(self,effect,kind):
        self.assertEqual(self.invoke(effect),2);self.assertFalse((self.out/'replay.json').exists());f=json.loads((self.out/'failure.json').read_text());self.assertEqual(f['error_type'],kind);return f
    def test_existing_success_rejected_unchanged(self):
        self.out.mkdir();p=self.out/'replay.json';p.write_text('{"result":"PASS","fixture":"old"}')
        before=p.read_bytes()
        with self.assertRaises(FileExistsError):self.invoke(lambda *a,**k:self.fail('checker executed'))
        self.assertEqual(p.read_bytes(),before)
    def test_existing_empty_or_stale_directory_rejected(self):
        self.out.mkdir();(self.out/'stale.stdout').write_text('old')
        with self.assertRaises(FileExistsError):self.invoke(lambda *a,**k:self.fail('checker executed'))
        self.assertFalse((self.out/'replay.json').exists())
    def test_nonzero(self):self.failed(lambda *a,**k:subprocess.CompletedProcess(a[0],7,'{}','failure fixture'),'RuntimeError')
    def test_malformed_json(self):self.failed(lambda *a,**k:subprocess.CompletedProcess(a[0],0,'{invalid',''),'JSONDecodeError')
    def test_timeout_preserves_partial_bytes(self):
        def effect(*a,**k):raise subprocess.TimeoutExpired(a[0],240,output=b'partial stdout\n',stderr=b'partial stderr\n')
        f=self.failed(effect,'TimeoutExpired');self.assertEqual(f['result'],'UNKNOWN');self.assertEqual(f['commands'][0]['status'],'UNKNOWN_TIMEOUT')
        self.assertEqual((self.out/'0-check_profiles.py.stdout').read_text(),'partial stdout\n');self.assertEqual((self.out/'0-check_profiles.py.stderr').read_text(),'partial stderr\n')
    def test_tamper_before_checker(self):
        p=self.root/'check_profiles.py';p.write_text(p.read_text()+'\n# deliberate fixture tamper\n')
        self.failed(lambda *a,**k:self.fail('checker executed'),'ValueError')
    def test_optimized_interpreter_rejected(self):
        p=subprocess.run([sys.executable,'-I','-O',str(self.root/'replay.py'),str(self.out)],capture_output=True,text=True,timeout=240)
        self.assertNotEqual(p.returncode,0);self.assertIn('Optimized Python is unsupported',p.stderr);self.assertFalse(self.out.exists())
    def test_normalization_preserves_semantics(self):
        a={'seconds':1,'nested':{'elapsed_seconds':2,'value':[1,2]}}
        b={'seconds':9,'nested':{'elapsed_seconds':8,'value':[1,2]}}
        self.assertEqual(self.runner.semantic_hash(a),self.runner.semantic_hash(b));b['nested']['value']=[2,1];self.assertNotEqual(self.runner.semantic_hash(a),self.runner.semantic_hash(b))
if __name__=='__main__':unittest.main()
