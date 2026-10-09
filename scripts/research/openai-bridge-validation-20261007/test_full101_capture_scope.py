"""Reject weakened inherited or additive acceptance scope without invoking Lean."""
import copy
import json
import unittest
from prepare_builder02_full90 import capsule
from prepare_builder02_full101 import PARENT, additions, make_successor, validate_expansion


class CaptureScope(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = capsule(PARENT / 'input-archive.tar.gz')
        cls.new = make_successor(cls.old)

    def reject(self, mutate):
        new = copy.deepcopy(self.new)
        manifest = json.loads(new['capture-manifest.json'])
        mutate(new, manifest)
        new['capture-manifest.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
        with self.assertRaises((AssertionError, KeyError)):
            validate_expansion(self.old, new)

    def test_exact_expansion(self):
        self.assertTrue(validate_expansion(self.old, self.new))

    def test_changed_parent_body(self):
        self.reject(lambda n, m: n.__setitem__(next(iter(m['project_sources'])), b'changed'))

    def test_dropped_parent_profile(self):
        self.reject(lambda n, m: m['requested_axioms'].pop(0))

    def test_dropped_new_profile(self):
        self.reject(lambda n, m: m['requested_axioms'].pop())

    def test_changed_source_stage(self):
        self.reject(lambda n, m: m['stages'][4]['argv'].pop(2))

    def test_dropped_checks_stage(self):
        self.reject(lambda n, m: m['stages'][5]['argv'].pop())

    def test_changed_cache_context(self):
        self.reject(lambda n, m: m['cache_provenance']['compiler'].__setitem__('sha256', '0' * 64))

    def test_changed_configuration(self):
        self.reject(lambda n, m: m['configs'].clear())

    def test_unowned_addition(self):
        self.reject(lambda n, m: m['owned_sources'].pop())

    def test_unpinned_external_scope(self):
        self.reject(lambda n, m: m['external_imports'].append('Unpinned.Package'))

    def test_changed_new_body(self):
        path = next(iter(additions()[0]))
        self.reject(lambda n, m: n.__setitem__(path, n[path] + b'\n'))

    def test_dropped_old_harness(self):
        self.reject(lambda n, m: n.__setitem__('fresh-integrated-axioms.lean', b''))


if __name__ == '__main__':
    unittest.main()
