"""Scope-loss mutation tests for the complete consumer/energy proposal."""
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_full104_consumer_energy_scope import PARENT, HARNESS, additions, make_successor, validate_expansion


class ScopeBoundary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old=capsule(PARENT/'input-archive.tar.gz')
        cls.new=make_successor(cls.old)

    def reject_manifest(self,mutation):
        new=dict(self.new);m=json.loads(new['capture-manifest.json']);mutation(m)
        new['capture-manifest.json']=json.dumps(m).encode()
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)

    def test_complete_scope(self):
        self.assertTrue(validate_expansion(self.old,self.new))

    def test_old_source_drift(self):
        new=dict(self.new);p=next(p for p in self.old if p.startswith('lean/'));new[p]+=b'\n'
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)

    def test_candidate_source_drift(self):
        new=dict(self.new);p=next(iter(additions()[0]));new[p]+=b'\n'
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)

    def test_profile_omission(self):
        self.reject_manifest(lambda m:m['requested_axioms'].pop(0))

    def test_stage_prefix_drift(self):
        self.reject_manifest(lambda m:m['stages'][4]['argv'].pop(2))

    def test_owned_scope_omission(self):
        self.reject_manifest(lambda m:m['owned_sources'].pop())

    def test_external_import_drift(self):
        self.reject_manifest(lambda m:m['external_imports'].append('Mathlib.Unpinned'))

    def test_package_pin_drift(self):
        def mutate(m):
            p=next(iter(m['cache_provenance']['package_sources']));m['cache_provenance']['package_sources'][p]='0'*64
        self.reject_manifest(mutate)

    def test_harness_omission(self):
        new=dict(self.new);new[HARNESS]=self.old[HARNESS]
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)


if __name__=='__main__':unittest.main()
