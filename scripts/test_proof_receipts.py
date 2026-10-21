#!/usr/bin/env python3
"""Test receipt consistency with synthetic fixtures, never proof acceptance."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from check_proof_receipts import RECEIPT, COLLECTION_INPUTS, check_receipt
import check_proof_receipts as cli
from mathematical_inputs import POLICY, project, phased_project, digest, read, lean_code

class BindingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name); self.package = self.root/'problems/fixture'
        (self.package/'scripts').mkdir(parents=True)
        (self.root/'scripts').mkdir()
        for rel in COLLECTION_INPUTS:(self.root/rel).write_text('# synthetic checker identity\n')
        self.cfg = {'registry':'scripts/registry.json','coverage':'scripts/coverage.py',
                    'axioms':'scripts/axioms.py','replay':'scripts/replay.py','oracle':'check.sh','target':'Fixture'}
        self.item = {'id':'fixture','path':'problems/fixture','lean':self.cfg}
        for path, text in {'Fixture.lean':'theorem result : True := by trivial\n',
                'lean-toolchain':'fixture-toolchain\n','lake-manifest.json':'{"fixture": true}\n',
                'lakefile.toml':'name = "fixture"\n[[lean_lib]]\nname = "Fixture"\n',
                'check.sh':'#!/bin/sh\nexit 1\n','scripts/coverage.py':'# static fixture\n',
                'scripts/axioms.py':'# static fixture\n','scripts/replay.py':'# static fixture\n',
                'README.md':'Synthetic fixture only.\n'}.items():
            (self.package/path).write_text(text)
        self.registry = [{'module':'Fixture','declaration':'result','type':'True','axioms':[],'oracle':True}]
        self.save_registry()
        self.receipt = {'schema':1,'policy':POLICY,'problem':'fixture',
            'main':project(self.package,self.cfg),'phased':[],
            'collection_inputs':{path:digest(read(self.root,path)) for path in COLLECTION_INPUTS},
            'evidence':[{'kind':'historical-clean','receipt_sha256':'1'*64,'acceptance_sha256':'2'*64,
                         'modules':['Fixture'],'declarations':['result']}]}
        self.save()
    def save_registry(self):
        (self.package/'scripts/registry.json').write_text(json.dumps(self.registry))
    def save(self):
        p=self.package/RECEIPT;p.parent.mkdir(exist_ok=True);p.write_text(json.dumps(self.receipt))
    def check(self):
        return check_receipt(self.root,self.item)
    def test_binding_match_is_not_proof_or_provenance(self):
        with patch('subprocess.run', side_effect=AssertionError('No subprocess allowed')):
            result=self.check()
        self.assertEqual(result['status'],'MATCH')
        self.assertFalse(result['proof_executed']);self.assertFalse(result['provenance_authenticated'])
    def test_collection_checker_change_fails(self):
        (self.root/'scripts/check.py').write_text('# modified checker identity\n')
        with self.assertRaises(ValueError):self.check()
    def test_cli_failure_replaces_stale_match(self):
        output=self.root/'output';output.mkdir();(output/'binding-check.json').write_text('{"status":"MATCH"}')
        (self.package/RECEIPT).unlink()
        with patch.object(cli,'ROOT',self.root), patch.object(cli,'load_registry',return_value={'fixture':self.item}), patch('sys.argv',['check','--problem','fixture','--output',str(output)]):
            with self.assertRaises(ValueError):cli.main()
        self.assertEqual(json.loads((output/'binding-check.json').read_text())['status'],'FAIL')
    def test_missing_receipt_fails(self):
        (self.package/RECEIPT).unlink()
        with self.assertRaises(ValueError):self.check()
    def test_modified_source_fails(self):
        (self.package/'Fixture.lean').write_text('theorem result : False := by trivial\n')
        with self.assertRaises(ValueError):self.check()
    def test_changed_comment_requires_current_raw_export_binding(self):
        (self.package/'Fixture.lean').write_text('-- revised comment\ntheorem result : True := by trivial\n')
        self.assertEqual(project(self.package,self.cfg)['mathematical_input_sha256'],self.receipt['main']['mathematical_input_sha256'])
        with self.assertRaises(ValueError):self.check()
    def test_docs_only_change_keeps_binding(self):
        (self.package/'README.md').write_text('Changed presentation only.\n')
        self.assertEqual(self.check()['status'],'MATCH')
    def test_checker_dependency_and_toolchain_changes_fail(self):
        for rel in ['scripts/axioms.py','lake-manifest.json','lean-toolchain','lakefile.toml']:
            with self.subTest(rel=rel):
                p=self.package/rel;old=p.read_bytes();p.write_bytes(old+b'\n')
                with self.assertRaises(ValueError):self.check()
                p.write_bytes(old)
    def test_statement_type_changes_fail(self):
        self.registry[0]['type']='False';self.save_registry()
        with self.assertRaises(ValueError):self.check()
    def test_oracle_marker_change_fails(self):
        self.registry[0]['oracle']=False;self.save_registry()
        with self.assertRaises(ValueError):self.check()
    def test_disallowed_axiom_fails(self):
        self.registry[0]['axioms']=['sorryAx'];self.save_registry()
        with self.assertRaises(ValueError):self.check()
    def test_legacy_missing_axioms_can_only_use_bound_map(self):
        del self.registry[0]['axioms'];self.save_registry()
        self.assertEqual(self.check()['status'],'MATCH')
    def test_missing_declaration_evidence_fails(self):
        self.receipt['evidence'][0]['declarations']=[];self.save()
        with self.assertRaises(ValueError):self.check()
    def test_missing_module_evidence_fails(self):
        self.receipt['evidence'][0]['modules']=[];self.save()
        with self.assertRaises(ValueError):self.check()
    def test_incomplete_evidence_union_fails(self):
        self.registry.append({'module':'Fixture','declaration':'other','type':'True','axioms':[],'oracle':False});self.save_registry()
        self.receipt['main']=project(self.package,self.cfg);self.save()
        with self.assertRaisesRegex(ValueError,'every main'):self.check()
    def test_foreign_evidence_names_fail(self):
        self.receipt['evidence'][0]['declarations']=['other'];self.save()
        with self.assertRaises(ValueError):self.check()
    def test_duplicate_evidence_names_fail(self):
        self.receipt['evidence'][0]['modules']*=2;self.save()
        with self.assertRaises(ValueError):self.check()
    def test_failed_or_unknown_evidence_kind_fails(self):
        for kind in ['failed','unknown','registered','docs']:
            self.receipt['evidence'][0]['kind']=kind;self.save()
            with self.assertRaises(ValueError):self.check()
    def test_changed_or_extra_envelope_fails(self):
        self.receipt['status']='PASS';self.save()
        with self.assertRaises(ValueError):self.check()
    def test_wrong_problem_fails(self):
        self.receipt['problem']='other';self.save()
        with self.assertRaises(ValueError):self.check()
    def test_symlink_source_fails(self):
        p=self.package/'Fixture.lean';p.rename(self.root/'target.lean');p.symlink_to(self.root/'target.lean')
        with self.assertRaises(ValueError):self.check()
    def test_traversal_input_fails(self):
        self.item['lean']={**self.cfg,'registry':'../registry.json'}
        with self.assertRaises(ValueError):self.check()
    def test_missing_phased_project_fails(self):
        self.item['phased_lean']=[{'path':'phase','plan':'scripts/phase.json','profile':'fixture'}]
        with self.assertRaises(ValueError):self.check()
    def test_extra_phased_project_fails(self):
        self.receipt['phased']=[{'path':'phase'}];self.save()
        with self.assertRaises(ValueError):self.check()
    def add_structural(self, code='import Fixture\n'):
        (self.package/'Aggregate.lean').write_text(code)
        lake=self.package/'lakefile.toml';lake.write_text(lake.read_text()+'\n[[lean_lib]]\nname = "Aggregate"\n')
        self.receipt['main']=project(self.package,self.cfg)
        self.receipt['evidence'].append({'kind':'structural-imports',
            'receipt_sha256':digest(read(self.package,'Aggregate.lean')),'acceptance_sha256':'3'*64,
            'modules':['Aggregate'],'declarations':[]})
        self.save()
    def test_structural_imports_bind_without_claiming_replay(self):
        self.add_structural('-- aggregate comment\n/- nested /- comment -/ -/\nimport Fixture\n')
        result=self.check();self.assertEqual(result['modules'],2)
        self.assertFalse(result['proof_executed']);self.assertFalse(result['provenance_authenticated'])
    def test_structural_source_hash_must_match(self):
        self.add_structural();self.receipt['evidence'][-1]['receipt_sha256']='0'*64;self.save()
        with self.assertRaisesRegex(ValueError,'source hash'):self.check()
    def test_structural_requires_exactly_one_module(self):
        self.add_structural();self.receipt['evidence'][-1]['modules']=['Fixture','Aggregate'];self.save()
        with self.assertRaisesRegex(ValueError,'one configured'):self.check()
    def test_structural_foreign_path_rejected(self):
        self.add_structural();self.receipt['evidence'][-1]['modules']=['../Aggregate'];self.save()
        with self.assertRaisesRegex(ValueError,'one configured'):self.check()
    def test_structural_cannot_cover_declarations(self):
        self.add_structural();self.receipt['evidence'][-1]['declarations']=['result'];self.save()
        with self.assertRaisesRegex(ValueError,'no declarations'):self.check()
    def test_structural_registered_declaration_rejected(self):
        self.add_structural();self.registry.append({'module':'Aggregate','declaration':'extra','type':'True','axioms':[],'oracle':False});self.save_registry()
        self.receipt['main']=project(self.package,self.cfg);self.save()
        with self.assertRaisesRegex(ValueError,'registered declarations'):self.check()
    def test_structural_duplicate_entry_rejected(self):
        self.add_structural();self.receipt['evidence'].append(dict(self.receipt['evidence'][-1]));self.save()
        with self.assertRaisesRegex(ValueError,'Duplicate structural'):self.check()
    def test_structural_cannot_overlap_nonstructural(self):
        self.add_structural();self.receipt['evidence'][0]['modules'].append('Aggregate');self.save()
        with self.assertRaisesRegex(ValueError,'distinct nonstructural'):self.check()
    def test_structural_external_or_uncovered_import_rejected(self):
        self.add_structural('import Missing\n')
        with self.assertRaisesRegex(ValueError,'accepted module coverage'):self.check()
    def test_structural_self_import_rejected(self):
        self.add_structural('import Aggregate\n')
        with self.assertRaisesRegex(ValueError,'accepted module coverage'):self.check()
    def test_structural_executable_commands_rejected(self):
        for code in ['import Fixture\nset_option autoImplicit true\n', 'import Fixture\ntheorem extra : True := by trivial\n', 'import Fixture; #check True\n', '#check "import Fixture"\n', '/- import Fixture -/\n']:
            with self.subTest(code=code):
                if not (self.package/'Aggregate.lean').exists():self.add_structural(code)
                else:
                    (self.package/'Aggregate.lean').write_text(code);self.receipt['main']=project(self.package,self.cfg)
                    self.receipt['evidence'][-1]['receipt_sha256']=digest(read(self.package,'Aggregate.lean'));self.save()
                with self.assertRaisesRegex(ValueError,'only import commands'):self.check()
    def add_phase(self):
        phase=self.package/'phase';(phase/'tools').mkdir(parents=True)
        for rel,text in {'Proof.lean':'theorem phase_result : True := by trivial\n',
                'tools/Hygiene.lean':'import Lean\n','lean-toolchain':'fixture\n',
                'lakefile.toml':'name="phase"\n','lake-manifest.json':'{}\n',
                'tools/run_phase.py':'# fixture\n','design-scope.json':'{"declarations":{"phase_result":"Proof"}}\n'}.items():
            (phase/rel).write_text(text)
        (self.package/'scripts/phase-plan.json').write_text('{}\n')
        self.item['phased_lean']=[{'path':'phase','profile':'fixture','plan':'scripts/phase-plan.json'}]
        descriptor={'path':'phase','registry':'design-scope.json','configuration':self.item['phased_lean'][0],
            'plan_sha256':digest(read(self.package,'scripts/phase-plan.json')),
            'sources':{name:{'sha256':digest(read(phase,name)),'lean_code_sha256':digest(lean_code(read(phase,name)))} for name in ['Proof.lean','tools/Hygiene.lean']},
            'inputs':{name:digest(read(phase,name)) for name in ['lean-toolchain','lakefile.toml','lake-manifest.json','tools/run_phase.py','design-scope.json']},
            'declarations':[{'name':'phase_result','module':'Proof','source_statement_sha256':digest(lean_code(read(phase,'Proof.lean'))),'axioms':[]}],
            'mathematical_input_sha256':'0'*64}
        self.receipt['phased']=[phased_project(self.package,descriptor)];self.save()
    def test_complete_phased_binding_matches(self):
        self.add_phase();self.assertEqual(self.check()['phased_projects'],1)
    def test_phased_profile_change_fails(self):
        self.add_phase();self.item['phased_lean'][0]=dict(self.item['phased_lean'][0],profile='other')
        with self.assertRaises(ValueError):self.check()
    def test_phased_plan_change_fails(self):
        self.add_phase();(self.package/'scripts/phase-plan.json').write_text('{"changed":true}')
        with self.assertRaises(ValueError):self.check()
    def test_phased_source_addition_fails(self):
        self.add_phase();(self.package/'phase/Extra.lean').write_text('theorem extra : True := by trivial')
        with self.assertRaises(ValueError):self.check()
    def test_phased_checker_omission_fails(self):
        self.add_phase();del self.receipt['phased'][0]['inputs']['tools/run_phase.py'];self.save()
        with self.assertRaises(ValueError):self.check()
    def test_phased_statement_omission_fails(self):
        self.add_phase();self.receipt['phased'][0]['declarations']=[];self.save()
        with self.assertRaises(ValueError):self.check()
    def test_wrong_mathematical_digest_fails(self):
        self.receipt['main']['mathematical_input_sha256']='0'*64;self.save()
        with self.assertRaises(ValueError):self.check()
    def test_duplicate_bound_declaration_fails(self):
        self.receipt['main']['projection']['declarations']*=2;self.save()
        with self.assertRaises(ValueError):self.check()

if __name__ == '__main__':unittest.main()
