"""Fault-injection tests for launch-relevant scope, with no Lean execution."""
import json
import unittest
from prepare_builder02_full93 import PARENT, OUTPUT, capsule, validate_expansion, HARNESS, ADDED


class ScopeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT / 'input-archive.tar.gz')
        cls.new = capsule(OUTPUT / 'input-archive.tar.gz')

    def reject(self, mutate):
        candidate = dict(self.new)
        mutate(candidate)
        with self.assertRaises((AssertionError, ValueError)):
            validate_expansion(self.old, candidate)

    def manifest_fault(self, mutation):
        def mutate(files):
            manifest = json.loads(files['capture-manifest.json'])
            mutation(manifest)
            files['capture-manifest.json'] = json.dumps(manifest).encode()
        self.reject(mutate)

    def test_positive(self):
        validate_expansion(self.old, self.new)

    def test_original_source_drift(self):
        rel = next(n for n in self.old if n.startswith('lean/') and n.endswith('.lean')
                   and 'SourceSize' not in n)
        self.reject(lambda f: f.__setitem__(rel, f[rel] + b'\n'))

    def test_missing_new_source(self):
        self.reject(lambda f: f.pop(ADDED))

    def test_new_source_drift(self):
        self.reject(lambda f: f.__setitem__(ADDED, f[ADDED] + b'\n'))

    def test_missing_harness_import(self):
        self.reject(lambda f: f.__setitem__(HARNESS, f[HARNESS].split(b'\n', 1)[1]))

    def test_narrowed_original_profiles(self):
        self.manifest_fault(lambda m: m['requested_axioms'].pop(0))

    def test_narrowed_stage(self):
        self.manifest_fault(lambda m: m['stages'][4]['argv'].pop(0))

    def test_changed_original_source_pin(self):
        self.manifest_fault(lambda m: m['project_sources'][next(iter(m['project_sources']))].update(sha256='0' * 64))

    def test_changed_config_pin(self):
        self.manifest_fault(lambda m: m['configs'][next(iter(m['configs']))].update(sha256='0' * 64))


if __name__ == '__main__':
    unittest.main()
