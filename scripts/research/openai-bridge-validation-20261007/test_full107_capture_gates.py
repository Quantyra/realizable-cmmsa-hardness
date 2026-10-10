"""Reject reduced or drifted repair scope without executing Lean."""
import copy
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_builder02_full107 import PARENT, REPAIR_FILE, SOURCE, validate_expansion
from prepare_builder02 import sha


class RepairScope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT/'input-archive.tar.gz')
        cls.good = dict(cls.old)
        cls.good[SOURCE] = REPAIR_FILE.read_bytes()
        manifest = json.loads(cls.old['capture-manifest.json'])
        manifest['project_sources'][SOURCE] = dict(sha256=sha(cls.good[SOURCE]), bytes=len(cls.good[SOURCE]))
        cls.good['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()

    def mutate_manifest(self, change):
        new = dict(self.good)
        manifest = json.loads(new['capture-manifest.json'])
        change(manifest)
        new['capture-manifest.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
        return new

    def reject(self, new):
        with self.assertRaises(AssertionError):
            validate_expansion(self.old, new)

    def test_exact_repair(self):
        self.assertTrue(validate_expansion(self.old, self.good))

    def test_second_source_edit(self):
        new = dict(self.good)
        rel = next(p for p in self.old if p.endswith('.lean') and p != SOURCE)
        new[rel] += b'\n'
        self.reject(new)

    def test_required_profile_omitted(self):
        self.reject(self.mutate_manifest(lambda m: m['requested_axioms'].pop()))

    def test_stage_narrowed(self):
        self.reject(self.mutate_manifest(lambda m: m['stages'].pop()))

    def test_stage_command_drift(self):
        self.reject(self.mutate_manifest(lambda m: m['stages'][0]['argv'].append('ForeignTarget')))

    def test_cache_drift(self):
        self.reject(self.mutate_manifest(lambda m: m['cache_provenance']['compiler'].update(sha256='0'*64)))

    def test_warning_suppression(self):
        new = dict(self.good)
        new[SOURCE] += b'\nset_option linter.unusedTactic false\n'
        self.reject(new)

    def test_wrong_proof_direction(self):
        new = dict(self.good)
        new[SOURCE] = self.old[SOURCE]
        self.reject(new)


if __name__ == '__main__':
    unittest.main()
