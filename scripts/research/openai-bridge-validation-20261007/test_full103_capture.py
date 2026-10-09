"""Reject scope drift in immutable successor inputs; no Lean execution."""
import copy
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_builder02_full103 import OUTPUT, PARENT, SOURCE, validate_expansion


class CaptureBoundary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT/'input-archive.tar.gz')
        cls.new = capsule(OUTPUT/'input-archive.tar.gz')

    def reject_manifest(self, mutation):
        new = dict(self.new)
        manifest = json.loads(new['capture-manifest.json'])
        mutation(manifest)
        new['capture-manifest.json'] = json.dumps(manifest).encode()
        with self.assertRaises(AssertionError): validate_expansion(self.old, new)

    def test_exact_successor(self):
        self.assertTrue(validate_expansion(self.old, self.new))

    def test_profile_omission(self):
        self.reject_manifest(lambda m:m['requested_axioms'].pop())

    def test_stage_command_drift(self):
        self.reject_manifest(lambda m:m['stages'][0]['argv'].append('OtherTarget'))

    def test_unrelated_source_change(self):
        new = dict(self.new)
        other = next(p for p in new if p.startswith('lean/') and p != SOURCE)
        new[other] += b'\n'
        with self.assertRaises(AssertionError): validate_expansion(self.old, new)

    def test_repair_body_drift(self):
        new = dict(self.new); new[SOURCE] += b'\n'
        with self.assertRaises(AssertionError): validate_expansion(self.old, new)

    def test_added_source(self):
        new = dict(self.new); new['lean/Other.lean'] = b'\n'
        with self.assertRaises(AssertionError): validate_expansion(self.old, new)

    def test_manifest_pin_drift(self):
        self.reject_manifest(lambda m:m['project_sources'][SOURCE].update(sha256='0'*64))

    def test_removed_source(self):
        self.reject_manifest(lambda m:m['project_sources'].pop(SOURCE))

    def test_configuration_drift(self):
        new = dict(self.new)
        other = next(p for p in new if p.endswith('lakefile.toml') or p.endswith('lakefile.lean'))
        new[other] += b'\n'
        with self.assertRaises(AssertionError): validate_expansion(self.old, new)


if __name__ == '__main__': unittest.main()
