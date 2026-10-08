"""Synthetic native-receipt tests for added-profile and harness custody gates."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
import full90_builder02_controller as controller


class SyntheticCommon:
    STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

    @staticmethod
    def diagnostic_counts(out, err):
        return {'errors': 0, 'unsolved_goals': 0}

    @staticmethod
    def axiom_profiles(out):
        return json.loads(out)

    @staticmethod
    def require_profiles(profiles):
        if 'original' not in profiles:
            raise ValueError('Missing original synthetic profile')


class ExpandedTerminal(unittest.TestCase):
    def fixture(self, directory, profiles, change_auxiliary=False):
        stage = {'index': 0, 'name': 'synthetic-only', 'argv': ['lake', 'env', 'lean', 'Synthetic.lean']}
        cache = {'objects': {}, 'package_sources': {}, 'core_sources': {}, 'compiler': {'sha256': 'synthetic'}}
        manifest = {'stages': [stage], 'requested_axioms': ['original', 'material'],
                    'project_sources': {}, 'configs': {}, 'cache_provenance': cache}
        out = json.dumps(profiles).encode()
        command = {'native_exit': 0, 'gcp_instance_id': controller.VM_ID, 'stage': stage,
                   'argv': ['timeout','--signal=TERM','--kill-after=20s','900s',*stage['argv']],
                   'stdout_sha256': hashlib.sha256(out).hexdigest().upper(),
                   'stderr_sha256': hashlib.sha256(b'').hexdigest().upper()}
        terminal = {'run': 'synthetic', 'host': {'id': controller.VM_ID, 'name': controller.VM},
                    'failure': None, 'native_exits': {'begin': 0, 'compile': 0, 'finish': 0}}
        auxiliary = {'Synthetic.lean': 'synthetic-harness-hash'}
        values = {'dedicated-worker-terminal.json': terminal, 'stage-0.command.json': command,
                  'resource-binding.json': {'auxiliary_inputs': auxiliary},
                  'auxiliary-before.json': auxiliary,
                  'auxiliary-after.json': {} if change_auxiliary else auxiliary,
                  'source-before.json': {}, 'source-after.json': {},
                  'verified-cache-provenance.json': cache, 'package-source-hashes.json': {},
                  'core-source-hashes.json': {}, 'compiler-identity.json': cache['compiler'], 'object-after.json': {}}
        data = {name: json.dumps(value).encode() for name, value in values.items()}
        data.update({'stage-0.native-exit': b'0', 'stage-0.stdout': out, 'stage-0.stderr': b''})
        path = Path(directory)/'synthetic.tar.gz'
        with tarfile.open(path, 'w:gz') as archive:
            for name, value in data.items():
                member = tarfile.TarInfo(name); member.size = len(value)
                archive.addfile(member, io.BytesIO(value))
        return path, manifest

    def test_added_standard_profile_and_auxiliary_custody_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, {'original': [], 'material': ['propext']})
            self.assertTrue(controller.audit_terminal(path, 'synthetic', manifest, SyntheticCommon)['compile_green'])

    def test_missing_added_profile_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, {'original': []})
            with self.assertRaisesRegex(RuntimeError, 'Full173'): controller.audit_terminal(path, 'synthetic', manifest, SyntheticCommon)

    def test_added_nonstandard_axiom_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, {'original': [], 'material': ['sorryAx']})
            with self.assertRaisesRegex(RuntimeError, 'Full173'): controller.audit_terminal(path, 'synthetic', manifest, SyntheticCommon)

    def test_changed_fresh_harness_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, {'original': [], 'material': []}, True)
            with self.assertRaisesRegex(RuntimeError, 'harness custody'): controller.audit_terminal(path, 'synthetic', manifest, SyntheticCommon)


if __name__ == '__main__':
    unittest.main()
