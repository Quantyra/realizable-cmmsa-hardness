"""Preservation and Unicode-loss fault injection; no Lean or cloud calls."""
import copy
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_builder02_full98 import PARENT,ADDED,make_successor,validate_expansion,validate_language
class Scope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.old=capsule(PARENT/'input-archive.tar.gz');cls.good=make_successor(cls.old)
    def reject(self,change):
        bad=copy.deepcopy(self.good);change(bad)
        with self.assertRaises((AssertionError,KeyError)):validate_expansion(self.old,bad)
    def mutate_manifest(self,bad,change):
        m=json.loads(bad['capture-manifest.json']);change(m);bad['capture-manifest.json']=(json.dumps(m,indent=2)+'\n').encode()
    def test_exact_two_source_addition_passes(self):self.assertTrue(validate_expansion(self.old,self.good))
    def test_unrelated_old_source_edit_rejected(self):
        path=next(p for p in self.old if p.startswith('lean/') and p not in ADDED);self.reject(lambda b:b.__setitem__(path,b[path]+b' '))
    def test_removed_source_rejected(self):self.reject(lambda b:b.pop(ADDED[0]))
    def test_extra_source_rejected(self):self.reject(lambda b:b.__setitem__('lean/Unexpected.lean',b''))
    def test_profile_narrowing_rejected(self):self.reject(lambda b:self.mutate_manifest(b,lambda m:m['requested_axioms'].pop()))
    def test_stage_narrowing_rejected(self):self.reject(lambda b:self.mutate_manifest(b,lambda m:m['stages'][4]['argv'].pop()))
    def test_context_change_rejected(self):self.reject(lambda b:self.mutate_manifest(b,lambda m:m['cache_provenance']['compiler'].__setitem__('sha256','0'*64)))
    def test_harness_change_rejected(self):self.reject(lambda b:b.__setitem__('fresh-integrated-axioms.lean',b'changed'))
    def test_unicode_ascii_replacement_rejected(self):
        for path in ADDED:
            text=self.good[path].decode();bad=text.encode('ascii',errors='replace')
            with self.assertRaises(AssertionError):validate_language(bad)
    def test_missing_plain_section_end_rejected(self):
        for path in ADDED:
            bad=self.good[path].replace(b'\nend\nend ',b'\nend ')
            with self.assertRaises(AssertionError):validate_language(bad)
    def test_invalid_utf8_rejected(self):
        with self.assertRaises(UnicodeDecodeError):validate_language(b'\xff')
    def test_placeholder_proof_rejected(self):
        bad=self.good[ADDED[1]]+b'\n-- sorry\n'
        with self.assertRaises(AssertionError):validate_language(bad)
if __name__=='__main__':unittest.main()
