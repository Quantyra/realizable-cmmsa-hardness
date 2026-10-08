"""Regression test for compiled sources absent from the fresh harness environment."""
import json
import unittest
from prepare_builder02_full92 import PARENT, HARNESS, IMPORTS, capsule, validate_repair, require_added_import_coverage


class ImportRepairTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT / 'input-archive.tar.gz')

    def repaired(self):
        new = dict(self.old)
        new[HARNESS] = IMPORTS + new[HARNESS]
        return new

    def test_original_missing_imports_rejected(self):
        with self.assertRaisesRegex(RuntimeError, 'does not import'):
            require_added_import_coverage(self.old)

    def test_repaired_harness_covers_all_five_requests(self):
        validate_repair(self.old, self.repaired())

    def test_all_imports_omitted_rejected(self):
        new = self.repaired()
        new[HARNESS] = self.old[HARNESS]
        with self.assertRaises(AssertionError):
            validate_repair(self.old, new)

    def test_profile_request_removed_rejected(self):
        new = self.repaired()
        new[HARNESS] = new[HARNESS].rsplit(b'#print axioms ', 1)[0]
        with self.assertRaises(AssertionError):
            validate_repair(self.old, new)

    def test_source_changed_rejected(self):
        new = self.repaired()
        manifest = json.loads(new['capture-manifest.json'])
        rel = next(iter(manifest['project_sources']))
        new[rel] += b'\n'
        with self.assertRaises(AssertionError):
            validate_repair(self.old, new)

    def test_stage_scope_changed_rejected(self):
        new = self.repaired()
        manifest = json.loads(new['capture-manifest.json'])
        manifest['stages'][4]['argv'].pop()
        new['capture-manifest.json'] = json.dumps(manifest).encode()
        with self.assertRaises(AssertionError):
            validate_repair(self.old, new)


if __name__ == '__main__':
    unittest.main()
