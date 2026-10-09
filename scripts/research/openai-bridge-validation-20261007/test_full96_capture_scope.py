"""Fault injection for exact additive capture boundaries; no Lean or GCP."""
import copy
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_builder02_full96 import PARENT,make_successor,validate_expansion,ADDED,HARNESS
class Scope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.old=capsule(PARENT/'input-archive.tar.gz');cls.good=make_successor(cls.old)
    def reject(self,mutate):
        bad=copy.deepcopy(self.good);mutate(bad)
        with self.assertRaises((AssertionError,KeyError)):validate_expansion(self.old,bad)
    def manifest(self,bad,change):
        m=json.loads(bad['capture-manifest.json']);change(m);bad['capture-manifest.json']=(json.dumps(m,indent=2)+'\n').encode()
    def test_exact_additive_scope_passes(self):self.assertTrue(validate_expansion(self.old,self.good))
    def test_old_source_change_rejected(self):
        path=next(p for p in self.old if p.startswith('lean/'));self.reject(lambda b:b.__setitem__(path,b[path]+b' '))
    def test_old_source_removal_rejected(self):
        path=next(p for p in self.old if p.startswith('lean/'));self.reject(lambda b:b.pop(path))
    def test_extra_source_rejected(self):self.reject(lambda b:b.__setitem__('lean/Unexpected.lean',b''))
    def test_new_candidate_change_rejected(self):self.reject(lambda b:b.__setitem__(ADDED[0],b[ADDED[0]]+b' '))
    def test_dropped_old_profile_rejected(self):self.reject(lambda b:self.manifest(b,lambda m:m['requested_axioms'].pop(0)))
    def test_duplicate_new_profile_rejected(self):self.reject(lambda b:self.manifest(b,lambda m:m['requested_axioms'].append(m['requested_axioms'][-1])))
    def test_dropped_stage_target_rejected(self):self.reject(lambda b:self.manifest(b,lambda m:m['stages'][4]['argv'].pop()))
    def test_stage_prefix_change_rejected(self):self.reject(lambda b:self.manifest(b,lambda m:m['stages'][0]['argv'].__setitem__(0,'different')))
    def test_harness_import_or_profile_loss_rejected(self):self.reject(lambda b:b.__setitem__(HARNESS,self.old[HARNESS]))
    def test_compiler_context_change_rejected(self):self.reject(lambda b:self.manifest(b,lambda m:m['cache_provenance']['compiler'].__setitem__('sha256','0'*64)))
    def test_configuration_change_rejected(self):self.reject(lambda b:self.manifest(b,lambda m:m['configs'].__setitem__('extra',{'sha256':'0'*64,'bytes':0})))
if __name__=='__main__':unittest.main()
