"""Fail closed on narrowed scope, altered parent bytes or dependency/runner drift."""
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_full106_product_energy_scope import PARENT, HARNESS, make_successor, validate_expansion


class Scope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT/'input-archive.tar.gz')
        cls.good = make_successor(cls.old)

    def manifest_mutation(self, mutate):
        new = dict(self.good)
        manifest = json.loads(new['capture-manifest.json'])
        mutate(manifest)
        new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
        return new

    def reject(self, new):
        with self.assertRaises(AssertionError):
            validate_expansion(self.old, new)

    def test_complete_addition(self):
        self.assertTrue(validate_expansion(self.old, self.good))

    def test_parent_source_altered(self):
        new = dict(self.good)
        name = next(p for p in self.old if p.endswith('.lean') and p != HARNESS)
        new[name] += b'\n'
        self.reject(new)

    def test_parent_profile_omitted(self):
        self.reject(self.manifest_mutation(lambda m: m['requested_axioms'].pop(0)))

    def test_new_profile_omitted(self):
        self.reject(self.manifest_mutation(lambda m: m['requested_axioms'].pop()))

    def test_stage_omitted(self):
        self.reject(self.manifest_mutation(lambda m: m['stages'].pop()))

    def test_stage_prefix_changed(self):
        self.reject(self.manifest_mutation(lambda m: m['stages'][4]['argv'].__setitem__(0, 'Foreign')))

    def test_dependency_cache_drift(self):
        self.reject(self.manifest_mutation(lambda m: m['cache_provenance']['compiler'].update(sha256='0'*64)))

    def test_source_pin_drift(self):
        self.reject(self.manifest_mutation(lambda m: next(iter(m['project_sources'].values())).update(sha256='0'*64)))

    def test_missing_candidate(self):
        new = dict(self.good)
        name = next(p for p in new if p not in self.old)
        new.pop(name)
        self.reject(new)

    def test_candidate_bytes_changed(self):
        new = dict(self.good)
        name = next(p for p in new if p not in self.old)
        new[name] += b'\n'
        self.reject(new)

    def test_harness_narrowed(self):
        new = dict(self.good)
        new[HARNESS] = self.old[HARNESS]
        self.reject(new)

    def test_untracked_capsule_file(self):
        new = dict(self.good)
        new['foreign.lean'] = b'foreign'
        self.reject(new)


if __name__ == '__main__':
    unittest.main()
