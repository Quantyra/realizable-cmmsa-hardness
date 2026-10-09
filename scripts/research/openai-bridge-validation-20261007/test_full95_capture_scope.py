"""Fault injection of exact call-only repair scope; no Lean execution."""
import json
import unittest
from prepare_builder02_full95 import PARENT, OUTPUT, SOURCE, NEW, capsule, validate_repair


class ScopeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT / 'input-archive.tar.gz')
        cls.new = capsule(OUTPUT / 'input-archive.tar.gz')

    def reject(self, mutate):
        files = dict(self.new)
        mutate(files)
        with self.assertRaises(AssertionError):
            validate_repair(self.old, files)

    def manifest_fault(self, mutate):
        def edit(files):
            manifest = json.loads(files['capture-manifest.json'])
            mutate(manifest)
            files['capture-manifest.json'] = json.dumps(manifest).encode()
        self.reject(edit)

    def test_positive(self):
        validate_repair(self.old, self.new)

    def test_other_source_drift(self):
        rel = next(n for n in self.old if n.startswith('lean/') and n != SOURCE)
        self.reject(lambda f: f.__setitem__(rel, f[rel] + b'\n'))

    def test_harness_drift(self):
        rel = 'fresh-integrated-axioms.lean'
        self.reject(lambda f: f.__setitem__(rel, f[rel] + b'\n'))

    def test_wrong_call_repair(self):
        self.reject(lambda f: f.__setitem__(SOURCE, f[SOURCE].replace(NEW, NEW.replace(b'A f;', b'A C;'))))

    def test_missing_profile(self):
        self.manifest_fault(lambda m: m['requested_axioms'].pop())

    def test_removed_stage_target(self):
        self.manifest_fault(lambda m: m['stages'][4]['argv'].pop())

    def test_bad_source_pin(self):
        self.manifest_fault(lambda m: m['project_sources'][SOURCE].update(sha256='0' * 64))

    def test_bad_config_pin(self):
        self.manifest_fault(lambda m: m['configs'][next(iter(m['configs']))].update(sha256='0' * 64))


if __name__ == '__main__':
    unittest.main()
