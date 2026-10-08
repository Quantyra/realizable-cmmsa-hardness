import unittest
from shared_worker import validate_spec


def spec():
    return {'thread': 'cmmsa_full83', 'run': 'cmmsa_a8_output_20261008T020000Z_12345678',
            'warm_run': 'cmmsa_a8_output_20261007T230522Z_6af6dc24',
            'helper_sha256': 'A' * 64, 'manifest_sha256': 'B' * 64,
            'warm_hashes': {'build/lib/lean/module.olean': 'C' * 64}}


class WorkerAdmission(unittest.TestCase):
    def test_valid_spec(self): validate_spec(spec())

    def test_escape_and_missing_provenance_rejected(self):
        for path in ('../outside', '/absolute', 'build/../outside', 'build\\outside', 'build//outside'):
            with self.subTest(path=path):
                value = spec(); value['warm_hashes'] = {path: 'C' * 64}
                with self.assertRaises(ValueError): validate_spec(value)
        value = spec(); value['warm_hashes'] = {}
        with self.assertRaises(ValueError): validate_spec(value)

    def test_same_workspace_and_bad_hash_rejected(self):
        value = spec(); value['warm_run'] = value['run']
        with self.assertRaises(ValueError): validate_spec(value)
        value = spec(); value['helper_sha256'] = 'unverified'
        with self.assertRaises(ValueError): validate_spec(value)


if __name__ == '__main__': unittest.main()
