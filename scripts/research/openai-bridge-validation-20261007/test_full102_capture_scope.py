"""Mutation checks for full-scope immutable warning-only preservation."""
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_builder02_full102 import PARENT,OUTPUT,validate_expansion


class Scope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old=capsule(PARENT/'input-archive.tar.gz')
        cls.new=capsule(OUTPUT/'input-archive.tar.gz')

    def mutate_manifest(self, mutation):
        new=dict(self.new);m=json.loads(new['capture-manifest.json']);mutation(m)
        new['capture-manifest.json']=json.dumps(m).encode()
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)

    def test_exact_successor(self):self.assertTrue(validate_expansion(self.old,self.new))
    def test_profile_drop(self):self.mutate_manifest(lambda m:m['requested_axioms'].pop())
    def test_stage_target_drop(self):self.mutate_manifest(lambda m:m['stages'][4]['argv'].pop())
    def test_owned_warning_scope_drop(self):self.mutate_manifest(lambda m:m['owned_sources'].pop())
    def test_external_import_add(self):self.mutate_manifest(lambda m:m['external_imports'].append('Mathlib.Unapproved'))
    def test_package_pin_change(self):
        self.mutate_manifest(lambda m:m['cache_provenance']['package_sources'].__setitem__(next(iter(m['cache_provenance']['package_sources'])),'0'*64))
    def test_unrelated_source_change(self):
        new=dict(self.new)
        rel=next(p for p in self.old if p.endswith('.lean') and self.old[p]==self.new[p])
        new[rel]+=b'\n'
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)
    def test_repair_source_change(self):
        new=dict(self.new)
        rel=next(p for p in self.old if p.endswith('.lean') and self.old[p]!=self.new[p])
        new[rel]+=b'\n'
        with self.assertRaises(AssertionError):validate_expansion(self.old,new)


if __name__=='__main__':unittest.main()
