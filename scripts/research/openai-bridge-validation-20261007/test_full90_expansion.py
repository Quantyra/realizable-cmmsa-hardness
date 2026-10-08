"""Negative scope fixtures; these are control tests, never Lean evidence."""
import json
import unittest
from prepare_builder02_full90 import PARENT, OUTPUT, REL, REQUEST, HARNESS, capsule, validate_expansion


class ExpansionScope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT/'input-archive.tar.gz')
        cls.new = capsule(OUTPUT/'input-archive.tar.gz')

    def altered_manifest(self, mutation):
        new = dict(self.new)
        manifest = json.loads(new['capture-manifest.json'])
        mutation(manifest)
        new['capture-manifest.json'] = json.dumps(manifest).encode()
        return new

    def test_exact_expansion_passes(self):
        self.assertEqual(len(validate_expansion(self.old, self.new)), 3)

    def test_original_stage_changed_rejected(self):
        new = self.altered_manifest(lambda m: m['stages'][4]['argv'].append('DifferentModule'))
        with self.assertRaisesRegex(RuntimeError, 'drift'): validate_expansion(self.old, new)

    def test_original_request_removed_rejected(self):
        new = self.altered_manifest(lambda m: m['requested_axioms'].pop(0))
        with self.assertRaisesRegex(RuntimeError, 'requests'): validate_expansion(self.old, new)

    def test_material_request_removed_rejected(self):
        new = self.altered_manifest(lambda m: m['requested_axioms'].remove(REQUEST))
        with self.assertRaisesRegex(RuntimeError, 'requests'): validate_expansion(self.old, new)

    def test_cache_provenance_changed_rejected(self):
        new = self.altered_manifest(lambda m: m['cache_provenance']['compiler'].update(sha256='0'*64))
        with self.assertRaisesRegex(RuntimeError, 'drift'): validate_expansion(self.old, new)

    def test_conditional_export_replacement_rejected(self):
        new = dict(self.new); new[REL] += b'\n-- changed source\n'
        with self.assertRaisesRegex(RuntimeError, 'export'): validate_expansion(self.old, new)

    def test_unrelated_source_changed_rejected(self):
        new = dict(self.new)
        path = next(p for p in new if p.startswith('lean/') and p != REL)
        new[path] += b'\n'
        with self.assertRaisesRegex(RuntimeError, 'file scope'): validate_expansion(self.old, new)

    def test_fresh172_harness_changed_rejected(self):
        new = dict(self.new); new[HARNESS] = new[HARNESS].replace(b'#print axioms ', b'#check ', 1)
        with self.assertRaisesRegex(RuntimeError, 'harness'): validate_expansion(self.old, new)

    def test_host_helper_changed_rejected(self):
        new = dict(self.new); new['cloud_capture.py'] += b'\n'
        with self.assertRaisesRegex(RuntimeError, 'file scope'): validate_expansion(self.old, new)


if __name__ == '__main__':
    unittest.main()
