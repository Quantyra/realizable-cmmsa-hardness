"""Fault injection against preservation and source/profile scope gates."""
import copy
import json
import unittest
from prepare_builder02_full91 import PARENT, OUTPUT, CANDIDATES, HARNESS, capsule, validate_expansion


class ExpansionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT / 'input-archive.tar.gz')
        cls.new = capsule(OUTPUT / 'input-archive.tar.gz')
        cls.derivation = json.loads((CANDIDATES / 'derivation.json').read_bytes())

    def reject(self, change):
        data = copy.deepcopy(self.new)
        change(data)
        with self.assertRaises(AssertionError):
            validate_expansion(self.old, data, self.derivation)

    def mutate_manifest(self, change):
        def mutate(data):
            manifest = json.loads(data['capture-manifest.json'])
            change(manifest)
            data['capture-manifest.json'] = json.dumps(manifest).encode()
        self.reject(mutate)

    def test_valid(self):
        validate_expansion(self.old, self.new, self.derivation)

    def test_original_source_drift(self):
        self.reject(lambda d: d.__setitem__(self.derivation['artifacts'][0]['parent_path'], b'changed'))

    def test_added_source_drift(self):
        self.reject(lambda d: d.__setitem__(self.derivation['artifacts'][0]['candidate_path'], b'changed'))

    def test_original_profile_removed(self):
        self.mutate_manifest(lambda m: m['requested_axioms'].pop(0))

    def test_original_stage_narrowed(self):
        self.mutate_manifest(lambda m: m['stages'][4]['argv'].pop(2))

    def test_other_stage_changed(self):
        self.mutate_manifest(lambda m: m['stages'][0]['argv'].append('Foreign'))

    def test_compiler_identity_changed(self):
        self.mutate_manifest(lambda m: m['cache_provenance']['compiler'].__setitem__('sha256', '0' * 64))

    def test_auxiliary_scope_removed(self):
        self.reject(lambda d: d.__setitem__(HARNESS, self.old[HARNESS]))

    def test_extra_source(self):
        self.reject(lambda d: d.__setitem__('lean/Foreign.lean', b'foreign'))


if __name__ == '__main__':
    unittest.main()
