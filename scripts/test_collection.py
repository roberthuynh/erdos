#!/usr/bin/env python3
"""Exercise problem admission, isolation, author protection and fail-closed checks."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import Mock
from check import inside, load_registry, run_problem, build_order, lean_imports
from select_problems import select
from check_collection import check_collection, prose
import hashlib

class CollectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name).resolve();p=self.root/'problems/60';p.mkdir(parents=True)
        self.package=p
        for file in ['README.md','RESULTS.md','docs.py']:(p/file).write_text('fixture\n')
        self.item={'id':'60','title':'Squares','topics':['graphs'],'path':'problems/60','checks':{'docs':[['python3','-B','docs.py']],'full':[['python3','-B','docs.py']]}}
        self.data={'schema_version':1,'problems':[self.item]};self.save()
        (self.root/'README.md').write_text('[60](problems/60/README.md)\nSTART\nMy own words.\nEND\n')
        (self.root/'CONTRIBUTING.md').write_text('Help\n');(self.root/'docs').mkdir();(self.root/'scripts').mkdir()
        (self.root/'scripts/author-prose.json').write_text(json.dumps({'files':[],'blocks':[{'path':'README.md','start':'START','end':'END','label':'voice','sha256':hashlib.sha256(prose('My own words.').encode()).hexdigest()}]}))
    def save(self):(self.root/'problems.json').write_text(json.dumps(self.data))
    def test_scope_selects_changed_problem_only(self):
        registry={'60':{},'585':{'lean':{}}}
        self.assertEqual(select(registry,['problems/60/README.md']),{'include':[{'id':'60','lean':False}]})
    def test_shared_checks_select_all_problems(self):
        registry={'60':{},'585':{'lean':{}}}
        self.assertEqual(len(select(registry,['scripts/check.py'])['include']),2)
    def test_root_prose_does_not_rebuild_mathematics(self):
        self.assertEqual(select({'585':{}},['README.md','docs/migration.md']),{'include':[]})
    def test_manual_run_checks_all(self):
        self.assertEqual(len(select({'585':{}},None)['include']),1)
    def test_written_only_problem_registers_without_lean(self):self.assertEqual(list(load_registry(self.root)),['60'])
    def test_unknown_package_rejected(self):
        (self.root/'problems/85').mkdir()
        with self.assertRaisesRegex(ValueError,'Unregistered'):load_registry(self.root)
    def test_duplicate_identifier_rejected(self):
        self.data['problems'].append(copy.deepcopy(self.item));self.save()
        with self.assertRaisesRegex(ValueError,'duplicate'):load_registry(self.root)
    def test_escape_or_mismatched_package_rejected(self):
        for path in ['../escape','problems/85','/tmp']:
            self.item['path']=path;self.save()
            with self.assertRaises(ValueError):load_registry(self.root)
    def test_symlink_not_admitted(self):
        (self.package/'docs.py').unlink();(self.package/'docs.py').symlink_to(self.root/'README.md')
        with self.assertRaisesRegex(ValueError,'Symlinks'):load_registry(self.root)
    def test_missing_or_empty_checks_rejected(self):
        self.item['checks']['full']=[];self.save()
        with self.assertRaisesRegex(ValueError,'empty'):load_registry(self.root)
    def test_incomplete_lean_configuration_rejected(self):
        self.item['lean']={'oracle':'docs.py'};self.save()
        with self.assertRaisesRegex(ValueError,'Incomplete'):load_registry(self.root)
    def test_prose_only_check_cannot_run_lean(self):
        run=Mock(return_value=subprocess.CompletedProcess([],0))
        run_problem(self.item,'full',self.root/'output',self.root,run)
        self.assertEqual(run.call_count,1)
        self.assertEqual(run.call_args.args[0],['timeout','240','python3','-B','docs.py'])
        self.assertEqual(run.call_args.kwargs['cwd'],self.package)
    def test_failure_stops_later_commands(self):
        self.item['checks']['docs']*=2
        run=Mock(return_value=subprocess.CompletedProcess([],1))
        with self.assertRaisesRegex(RuntimeError,'FAIL'):run_problem(self.item,'docs',self.root/'output',self.root,run)
        self.assertEqual(run.call_count,1)
    def test_timeout_is_unknown(self):
        run=Mock(side_effect=subprocess.TimeoutExpired('fixture',245))
        with self.assertRaisesRegex(RuntimeError,'UNKNOWN'):run_problem(self.item,'docs',self.root/'output',self.root,run)
        receipt=json.loads((self.root/'output/receipt.json').read_text());self.assertEqual(receipt['status'],'UNKNOWN')
    def lean_fixture(self, omit_oracle_marker=False):
        self.item['lean']={'registry':'headlines.json','coverage':'coverage.py','axioms':'axioms.py','replay':'replay.py','oracle':'check.sh','target':'Root'}
        (self.package/'Root.lean').write_text('import Leaf\n')
        (self.package/'Leaf.lean').write_text('import Mathlib\n')
        (self.package/'headlines.json').write_text(json.dumps([{'module':'Leaf','declaration':'result','oracle':True}]))
        def fake(argv, **kwargs):
            command=argv[2:]
            text=''
            if command==['python3','-B','coverage.py','--list']:text='Root\nLeaf\n'
            elif command==['python3','-B','axioms.py']:text='STATEMENTS: PASS'
            elif command[0]=='bash' and not omit_oracle_marker:text='RESULT: PASS'
            elif 'replay.py' in command:text='KERNEL REPLAY: PASS'
            kwargs['stdout'].write(text)
            return subprocess.CompletedProcess(argv,0)
        return Mock(side_effect=fake)
    def test_full_lean_builds_modules_and_checks_every_gate(self):
        run=self.lean_fixture()
        records=run_problem(self.item,'full',self.root/'output',self.root,run)
        commands=[x['command'] for x in records]
        self.assertEqual([c for c in commands if c[0]=='lake'],[['lake','build','Leaf'],['lake','build','Root']])
        self.assertEqual(sum('replay.py' in c for c in commands),2)
        self.assertTrue(all(x['status']=='PASS' for x in records))
    def test_zero_exit_without_oracle_pass_is_failure(self):
        run=self.lean_fixture(omit_oracle_marker=True)
        with self.assertRaisesRegex(RuntimeError,'FAIL'):run_problem(self.item,'full',self.root/'output',self.root,run)
        self.assertFalse(any('replay.py' in call.args[0] for call in run.call_args_list))
    def test_timeout_exit_code_remains_unknown(self):
        run=Mock(return_value=subprocess.CompletedProcess([],124))
        with self.assertRaisesRegex(RuntimeError,'UNKNOWN'):run_problem(self.item,'docs',self.root/'output',self.root,run)
    def test_build_order_dependencies_first_and_exact_set(self):
        for name,text in {'Root':'import Parent', 'Parent':'import Child', 'Child':'import Mathlib', 'Other':''}.items():
            (self.package/(name+'.lean')).write_text(text)
        order=build_order(self.package,['Root','Parent','Other','Child'],'Root')
        self.assertEqual(order,['Child','Other','Parent','Root'])
        self.assertEqual(order,build_order(self.package,['Child','Other','Parent','Root'],'Root'))
        self.assertEqual(set(order),{'Root','Parent','Other','Child'})
    def test_import_parser_ignores_comments_and_strings(self):
        text='import Child /- import Fake /- nested -/ -/\n-- import Hidden\ndef s := "escaped \\" text\nimport StringFake"\npublic import Mathlib\n'
        self.assertEqual(lean_imports(text),['Child','Mathlib'])
    def test_build_order_rejects_cycle_and_duplicates(self):
        (self.package/'Root.lean').write_text('import Child')
        (self.package/'Child.lean').write_text('import Root')
        with self.assertRaisesRegex(ValueError,'Cycle'):build_order(self.package,['Child','Root'],'Root')
        with self.assertRaisesRegex(ValueError,'duplicate'):build_order(self.package,['Root','Root'],'Root')
    def test_build_order_rejects_missing_and_unconfigured_sources(self):
        (self.package/'Root.lean').write_text('import Child')
        with self.assertRaisesRegex(ValueError,'Missing'):build_order(self.package,['Root','Child'],'Root')
        (self.package/'Child.lean').write_text('')
        with self.assertRaisesRegex(ValueError,'Unconfigured'):build_order(self.package,['Root'],'Root')
    def test_import_parser_rejects_unterminated_masks(self):
        for text in ['/- unterminated','"unterminated']:
            with self.assertRaisesRegex(ValueError,'Unterminated'):lean_imports(text)
    def test_navigation_and_prose_pass(self):self.assertEqual(check_collection(self.root),1)
    def test_author_words_cannot_silently_change(self):
        p=self.root/'README.md';p.write_text(p.read_text().replace('My own words.','Generated replacement.'))
        with self.assertRaisesRegex(ValueError,'author prose changed'):check_collection(self.root)
    def test_broken_heading_link_fails(self):
        (self.root/'CONTRIBUTING.md').write_text('[bad](README.md#missing)')
        with self.assertRaisesRegex(ValueError,'Broken local fragment'):check_collection(self.root)
    def test_broken_link_fails(self):
        (self.root/'CONTRIBUTING.md').write_text('[bad](missing.md)')
        with self.assertRaisesRegex(ValueError,'Broken local link'):check_collection(self.root)

if __name__=='__main__':unittest.main()
