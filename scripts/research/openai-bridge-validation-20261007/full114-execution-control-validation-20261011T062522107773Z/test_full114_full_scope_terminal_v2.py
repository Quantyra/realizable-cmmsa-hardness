"""Synthetic Full114 evidence rejection tests. No Lean, GCP, or genuine native result."""
import copy
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import full114_builder02_controller as controller
import full114_native_audit as native_audit
import full114_verify as verifier
import full114_worker as worker
from prepare_builder02_full91 import PARENT as MATERIAL_PARENT, REQUESTS as SOURCE_REQUESTS
from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS
from prepare_builder02_full109 import REQUESTS as BRIDGE_REQUESTS
from prepare_complete_operator_scope_v2 import additions

sys.path.insert(0, 'C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/docs/a8-gcp/r1007')
import common


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


class FullScopeEvidenceBoundary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((controller.ROOT / 'capture-manifest.json').read_bytes())
        cls.binding = json.loads((controller.ROOT / 'resource-binding.json').read_bytes())

    def fixture(self, directory, mutation=None, missing_profile=None, nonstandard_profile=None):
        manifest = copy.deepcopy(self.manifest)
        profile_names = list(dict.fromkeys(manifest['requested_axioms'] + list(common.REQUESTED_AXIOMS)))
        profiles = [name for name in profile_names if name != missing_profile]
        output = ''.join("'" + name + "' depends on axioms: [" +
                         ('sorryAx' if name == nonstandard_profile else 'propext, Classical.choice, Quot.sound') +
                         ']\n' for name in profiles).encode()
        data = {}
        for stage in manifest['stages']:
            i = stage['index']
            out = output if i == 6 else b''
            command = dict(native_exit=0, gcp_instance_id=controller.VM_ID, stage=stage,
                           argv=['timeout', '--signal=TERM', '--kill-after=20s', '900s', *stage['argv']],
                           stdout_sha256=sha(out), stderr_sha256=sha(b''))
            data.update({f'stage-{i}.native-exit': b'0', f'stage-{i}.command.json': json.dumps(command).encode(),
                         f'stage-{i}.stdout': out, f'stage-{i}.stderr': b''})
        sources = {rel: row['sha256'] for rel, row in manifest['project_sources'].items()}
        sources.update({rel: row['sha256'] for rel, row in manifest['configs'].items()})
        cache = manifest['cache_provenance']
        objects = {
            'dedicated-worker-terminal.json': dict(run='synthetic_full114_not_native',
                host=dict(id=controller.VM_ID, name=controller.VM), failure=None,
                native_exits=dict(begin=0, compile=0, finish=0)),
            'resource-binding.json': self.binding,
            'source-before.json': sources, 'source-after.json': sources,
            'auxiliary-before.json': self.binding['auxiliary_inputs'],
            'auxiliary-after.json': self.binding['auxiliary_inputs'],
            'verified-cache-provenance.json': cache, 'package-source-hashes.json': cache['package_sources'],
            'core-source-hashes.json': cache['core_sources'], 'compiler-identity.json': cache['compiler'],
            'object-after.json': cache['objects']}
        data.update({name: json.dumps(value).encode() for name, value in objects.items()})
        if mutation:
            mutation(data)
        path = Path(directory) / 'synthetic-full114-not-native.tar.gz'
        with tarfile.open(path, 'w:gz') as archive:
            for name, value in data.items():
                member = tarfile.TarInfo(name)
                member.size = len(value)
                archive.addfile(member, io.BytesIO(value))
        return path, manifest

    def audit(self, path, manifest):
        return controller.audit_terminal(path, 'synthetic_full114_not_native', manifest, common)

    def test_full347_synthetic_fixture_reaches_all_seven_stages(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory)
            result = self.audit(path, manifest)
        self.assertTrue(result['compile_green'])
        self.assertEqual(len(result['stages']), 7)
        self.assertEqual(result['axiom_profiles'], len(set(self.manifest['requested_axioms']) | set(common.REQUESTED_AXIOMS)))
        self.assertTrue(result['reviews_required'])

    def test_missing_first_or_last_added_profile_rejected(self):
        for name in (self.manifest['requested_axioms'][261], self.manifest['requested_axioms'][-1]):
            with self.subTest(profile=name), tempfile.TemporaryDirectory() as directory:
                path, manifest = self.fixture(directory, missing_profile=name)
                with self.assertRaisesRegex(RuntimeError, 'Full347 standard-axiom scope'):
                    self.audit(path, manifest)

    def test_missing_original_profile_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, missing_profile=next(name for name in self.manifest['requested_axioms'] if name in common.REQUESTED_AXIOMS))
            with self.assertRaisesRegex(ValueError, 'Missing axiom profiles'):
                self.audit(path, manifest)

    def test_nonstandard_added_profile_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, nonstandard_profile=self.manifest['requested_axioms'][-1])
            with self.assertRaisesRegex(RuntimeError, 'Full347 standard-axiom scope'):
                self.audit(path, manifest)

    def test_source_harness_cache_and_toolchain_drift_rejected(self):
        added_path = 'lean/PvNP/RealizableHardness/ExactPhiEigenrelation.lean'
        original_path = next(iter(self.manifest['project_sources']))
        config_path = next(iter(self.manifest['configs']))
        cases = [('source-before.json', original_path), ('source-after.json', original_path),
                 ('source-before.json', added_path), ('source-after.json', added_path),
                 ('source-after.json', config_path), ('auxiliary-before.json', 'fresh-integrated-axioms.lean'),
                 ('auxiliary-after.json', 'fresh-integrated-axioms.lean'),
                 ('verified-cache-provenance.json', 'run'), ('compiler-identity.json', 'sha256'),
                 ('package-source-hashes.json', next(iter(self.manifest['cache_provenance']['package_sources']))),
                 ('core-source-hashes.json', next(iter(self.manifest['cache_provenance']['core_sources']))),
                 ('object-after.json', next(iter(self.manifest['cache_provenance']['objects'])))]
        for filename, key in cases:
            def mutate(data):
                value = json.loads(data[filename])
                value[key] = 'synthetic-drift'
                data[filename] = json.dumps(value).encode()
            with self.subTest(file=filename, key=key), tempfile.TemporaryDirectory() as directory:
                path, manifest = self.fixture(directory, mutate)
                with self.assertRaises(RuntimeError):
                    self.audit(path, manifest)

    def test_absent_stage_receipt_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path, manifest = self.fixture(directory, lambda data: data.pop('stage-6.native-exit'))
            with self.assertRaises(KeyError):
                self.audit(path, manifest)

    def test_cumulative_qualification_scope_matches_actual_package(self):
        original_root = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/docs/a8-gcp/r1007/captures/capture-full-a22-hc46-83/inputs')
        original = json.loads((original_root / 'capture-manifest.json').read_bytes())
        repair = json.loads((MATERIAL_PARENT / 'source-expansion.json').read_bytes())
        extra = SOURCE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS + additions()[1]
        self.assertEqual(self.manifest['requested_axioms'], original['requested_axioms'] + [repair['additional_profile']] + extra)
        self.assertEqual(len(set(self.manifest['project_sources']) - set(original['project_sources'])), 50)
        self.assertEqual(len(additions()[1]), 86)
        normalized = copy.deepcopy(self.manifest)
        normalized['vm'] = original['vm']
        for field in ('requested_axioms', 'stages', 'owned_sources', 'external_imports', 'project_sources'):
            normalized[field] = original[field]
        self.assertEqual(normalized, original)

    def test_local_worker_and_verifier_rejected_before_filesystem_or_process_use(self):
        with patch.object(sys, 'platform', 'win32'):
            for call in (lambda: worker.execute('nonexistent', 'invalid'), lambda: verifier.verify('nonexistent')):
                with self.assertRaisesRegex(RuntimeError, 'GCP Linux required'):
                    call()

    def test_qualification_rejects_foreign_root_before_any_action(self):
        with self.assertRaisesRegex(RuntimeError, 'Unexpected material resource root'):
            native_audit.main(controller.ROOT.parent / 'foreign-root')


if __name__ == '__main__':
    unittest.main()
