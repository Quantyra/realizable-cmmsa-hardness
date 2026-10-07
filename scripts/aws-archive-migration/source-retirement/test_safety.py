"""Synthetic regressions. No real credentials, sockets, payloads or cloud calls."""
import copy
import json
import sys
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parent))
from safety import *
from inventory import full_inventory, compare_inventory, compare_version_metadata
from retirement import run, permissions, hash_reuse_scope

REAL = json.loads((Path(__file__).parent / 'evidence/bound-allowlist.json').read_bytes())


class Fixture:
    def __init__(self, directory):
        self.a = copy.deepcopy(REAL)
        # Full205 synthetic identities; no real objects or payloads enter the fixture.
        self.a['rows'] = [{'key': f'fixture/{i}', 'source_version': f's{i}',
                           'destination_version': f'd{i}', 'source_etag': '"etag"',
                           'bytes': 1, 'sha256': 'a'*64} for i in range(205)]
        self.source = {'rows': [{'key': r['key'], 'version': r['source_version'], 'bytes': 1}
                                for r in self.a['rows']], 'markers': [], 'uploads': []}
        self.dest = {'rows': [{'key': r['key'], 'version': r['destination_version'], 'bytes': 1}
                              for r in self.a['rows']], 'markers': [], 'uploads': []}
        self.calls = []
        self.expired = False
        self.principals = PRINCIPALS.copy()
        self.config = {SOURCE: {'fixture': 'source'}, DEST: {'fixture': 'destination'}}
        self.scope = {'type': 'archive-independent-hash-reuse-v1',
                      'reviewer_role': 'root-independent-verifier', 'versions': 205,
                      'encrypted_chunks': 105, 'recovery_catalogs': 44,
                      'authentication_proof_sha256': 'a'*64, 'version_metadata_sha256': 'b'*64,
                      'scope': {'packet_sha256': self.a['packet_sha256'], 'source': BUCKET,
                                'destination': TARGET, 'rows': self.a['rows'],
                                'catalogs': self.a['catalogs'], 'packet_artifacts': self.a['packet_artifacts']}}
        resources = [f'arn:aws:s3:::{BUCKET}/{r["key"]}' for r in self.a['rows']]
        self.permission = {'IsTruncated': False, 'EvaluationResults': [
            {'EvalActionName': action, 'EvalDecision': 'allowed', 'ResourceSpecificResults': [
                {'EvalResourceName': r, 'EvalResourceDecision': 'allowed'} for r in names]}
            for action, names in [('s3:DeleteObjectVersion', resources),
                                  ('s3:DeleteBucket', [f'arn:aws:s3:::{BUCKET}'])]]}
        self.g = {'_gate_sha256': 'gate', '_allowlist_sha256': 'allowlist',
                  'execution_state_directory': str(directory),
                  'hash_reuse_scope_sha256': digest(self.scope),
                  'version_metadata_sha256': 'b'*64, 'permission_proof_sha256': digest(self.permission),
                  'source_configuration_sha256': digest(self.config[SOURCE]),
                  'destination_configuration_sha256': digest(self.config[DEST])}
        self.journal = Journal(Path(directory)/'journal', 'gate', 'allowlist')
        self.on_deps = lambda: None
        self.on_auth = lambda: None
        self.on_delete = lambda: None
        self.lost = False
        self.leave_present = False

    def authorize(self):
        self.on_auth()
        require(not self.expired, 'ROOT_GATE_EXPIRED')
        return self.g

    def identities(self):
        return self.principals

    def dependencies(self):
        self.on_deps()

    def configuration(self, account):
        return None if account == SOURCE and self.source is None else self.config[account]

    def permissions(self):
        return self.permission

    def hash_scope(self):
        return self.scope

    def source_state(self):
        return self.source

    def destination_state(self):
        return self.dest

    def metadata(self, row, present):
        # Enforce actual per-version baseline in fake service, not a stale true flag.
        require(not getattr(self, 'bad_metadata', False), 'METADATA_DRIFT')

    def delete_version(self, row):
        self.calls.append(('version', row['source_version']))
        if not self.leave_present:
            self.source['rows'] = [r for r in self.source['rows'] if r['version'] != row['source_version']]
        self.on_delete()
        if self.lost:
            raise TimeoutError()
        return {'VersionId': row['source_version']}

    def delete_bucket(self):
        self.calls.append(('bucket', BUCKET))
        if not self.leave_present:
            self.source = None
        if self.lost:
            raise TimeoutError()

    def run(self, execute=False):
        return run(self, self.a, self.authorize, self.journal, execute)


class EngineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.f = Fixture(self.temp.name)

    def blocked(self, code, execute=False):
        with self.assertRaisesRegex(Stop, code):
            self.f.run(execute)

    def test_check_only_no_mutations_or_journal(self):
        self.assertEqual(self.f.run()['mode'], 'check-only')
        self.assertEqual(self.f.calls, [])
        self.assertFalse(self.f.journal.file.exists())

    def test_runner_enforces_shared_lock(self):
        lock = self.f.journal.file.parent/'execution.lock'
        lock.write_bytes(b'preserved-stale-or-live-owner')
        with self.assertRaises(FileExistsError):
            self.f.run(True)
        self.assertEqual(lock.read_bytes(), b'preserved-stale-or-live-owner')
        self.assertEqual(self.f.calls, [])

    def test_cached_journal_cannot_bypass_current_chain(self):
        Journal(self.f.journal.file, 'gate', 'allowlist').append('intent', 'bucket', BUCKET)
        self.blocked('JOURNAL_CHANGED_BEFORE_LOCK', True)
        self.assertEqual(self.f.calls, [])

    def test_full205_success_closing_observation(self):
        result = self.f.run(True)
        self.assertEqual(len(self.f.calls), 206)
        self.assertEqual(result['observation']['destination_versions'], 205)
        self.assertFalse(result['observation']['distributed_atomicity'])
        self.assertEqual(self.f.journal.events[-1]['details']['observation'], result['observation'])

    def test_lost_reply_absence_no_duplicate_wire(self):
        self.f.lost = True
        self.f.run(True)
        self.assertEqual(len(self.f.calls), 206)
        self.f.run(True)
        self.assertEqual(len(self.f.calls), 206)

    def test_ambiguous_present_preserves_no_retry(self):
        self.f.leave_present = True
        self.blocked('AMBIGUOUS_VERSION_DELETE_NO_RETRY', True)
        before = self.f.journal.file.read_bytes()
        self.blocked('AMBIGUOUS_VERSION_DELETE_NO_RETRY', True)
        self.assertEqual(len(self.f.calls), 1)
        self.assertEqual(before, self.f.journal.file.read_bytes())

    def test_empty_recreated_bucket_blocks(self):
        self.f.run(True)
        self.f.source = {'rows': [], 'markers': [], 'uploads': []}
        self.blocked('BUCKET_REAPPEARANCE', True)
        self.assertEqual(len(self.f.calls), 206)

    def test_recreated_bucket_extra_data_blocks(self):
        self.f.run(True)
        self.f.source = {'rows': [{'key': 'other', 'version': 'new', 'bytes': 1}], 'markers': [], 'uploads': []}
        self.blocked('BUCKET_REAPPEARANCE', True)

    def test_missing_destination_after_complete_blocks(self):
        self.f.run(True)
        self.f.dest['rows'].pop()
        self.blocked('DESTINATION_CUSTODY_LOST', True)

    def test_shared_source_data_blocks(self):
        self.f.source['rows'].append({'key': 'shared', 'version': 'new', 'bytes': 1})
        self.blocked('SHARED_DATA_OR_SOURCE_DRIFT', True)
        self.assertEqual(self.f.calls, [])

    def test_source_markers_block(self):
        self.f.source['markers'].append({'key': 'marker'})
        self.blocked('SOURCE_MARKERS_OR_UPLOADS')

    def test_inflight_upload_blocks(self):
        self.f.dest['uploads'].append({'key': 'upload'})
        self.blocked('DESTINATION_EXTRAS')

    def test_source_unexpected_absence_blocks(self):
        self.f.source['rows'].pop()
        self.blocked('UNEXPECTED_VERSION_ABSENCE')

    def test_wrong_principal(self):
        self.f.principals[SOURCE] = 'another-user'
        self.blocked('CURRENT_PRINCIPAL')

    def test_principal_drift_after_delete_blocks_second(self):
        self.f.on_delete = lambda: self.f.principals.update({SOURCE: 'new'})
        self.blocked('CURRENT_PRINCIPAL', True)
        self.assertEqual(len(self.f.calls), 1)

    def test_expiry_during_dependencies_no_mutation(self):
        self.f.on_deps = lambda: setattr(self.f, 'expired', True)
        self.blocked('ROOT_GATE_EXPIRED', True)
        self.assertEqual(self.f.calls, [])

    def test_expiry_after_durable_intent_no_mutation(self):
        self.f.on_auth = lambda: setattr(self.f, 'expired', bool(self.f.journal.events))
        self.blocked('ROOT_GATE_EXPIRED', True)
        self.assertEqual(self.f.calls, [])
        self.assertEqual(len(self.f.journal.events), 1)

    def test_expiry_after_terminal_no_success(self):
        self.f.on_auth = lambda: setattr(self.f, 'expired', any(e['kind'] == 'terminal' for e in self.f.journal.events))
        self.blocked('ROOT_GATE_EXPIRED', True)
        self.assertEqual(self.f.journal.events[-1]['kind'], 'terminal')

    def test_last_dependency_destination_loss_blocks_terminal(self):
        self.f.on_deps = lambda: self.f.dest['rows'].clear() if self.f.source is None else None
        self.blocked('DESTINATION_CUSTODY_LOST', True)
        self.assertFalse(any(e['kind'] == 'terminal' for e in self.f.journal.events))

    def test_checkonly_late_dependency_expiry(self):
        count = [0]
        def late():
            count[0] += 1
            self.f.expired = count[0] == 2
        self.f.on_deps = late
        self.blocked('ROOT_GATE_EXPIRED')

    def test_denied_permission_checkonly(self):
        self.f.permission['EvaluationResults'][0]['EvalDecision'] = 'explicitDeny'
        self.blocked('PERMISSION_DENIED')

    def test_permission_missing_resource(self):
        self.f.permission['EvaluationResults'][0]['ResourceSpecificResults'].pop()
        self.blocked('PERMISSION_RESOURCE_COVERAGE')

    def test_permission_missing_context(self):
        self.f.permission['EvaluationResults'][0]['ResourceSpecificResults'][0]['MissingContextValues'] = ['context']
        self.blocked('PERMISSION_RESOURCE_DENIED')

    def test_permission_truncation(self):
        self.f.permission['IsTruncated'] = True
        self.blocked('PERMISSION_TRUNCATED')

    def test_config_drift(self):
        self.f.config[SOURCE]['fixture'] = 'changed'
        self.blocked('CONFIGURATION_DRIFT')

    def test_header_tag_acl_drift(self):
        self.f.bad_metadata = True
        self.blocked('METADATA_DRIFT')

    def test_stale_verified_flag_not_hash_scope(self):
        self.f.scope = {'verified': True}
        with self.assertRaises((KeyError, Stop)):
            self.f.run()
        self.assertEqual(self.f.calls, [])

    def test_changed_exact_hash_identity(self):
        self.f.scope = copy.deepcopy(self.f.scope)
        self.f.scope['scope']['rows'][0]['destination_version'] = 'changed'
        self.blocked('INDEPENDENT_EXACT_HASH_SCOPE_REQUIRED')

    def test_ambiguous_bucket_present_no_retry(self):
        original = self.f.delete_bucket
        def ambiguous():
            self.f.leave_present = True
            original()
        self.f.delete_bucket = ambiguous
        self.blocked('AMBIGUOUS_BUCKET_DELETE_NO_RETRY', True)
        self.blocked('BUCKET_REAPPEARANCE', True)
        self.assertEqual(len(self.f.calls), 206)


class DurableAndScopeTests(unittest.TestCase):
    def gate_fixture(self):
        allowlist = encoded(REAL)
        blobs = {'docs/aws-migration-2026-10-06/archive-source-retirement-allowlist.json': allowlist}
        pins = []
        for kind in sorted(KINDS):
            proof_path = f'docs/aws-migration-2026-10-06/fixture-proof-{kind}.json'
            blobs[proof_path] = encoded({'synthetic': True, 'kind': kind})
            data = {'type': 'archive-retirement-attestation-v1', 'kind': kind, 'decision': 'ACCEPT',
                    'packet_sha256': PACKET, 'allowlist_sha256': digest(allowlist),
                    'observed_at': '2026-10-07T12:00:00Z', 'valid_until': '2026-10-07T13:00:00Z',
                    'reviewer_role': 'root-independent-verifier',
                    'underlying_proofs': [{'path': proof_path, 'sha256': digest(blobs[proof_path])}]}
            file = f'docs/aws-migration-2026-10-06/fixture-{kind}.json'
            blobs[file] = encoded(data)
            pins.append({'kind': kind, 'path': file, 'sha256': digest(blobs[file])})
        g = {'type': 'archive-retirement-root-gate-v1', 'authorized': True, 'decision': 'ACCEPT',
             'execution_state_directory': str(Path.home()/'.quantyra/aws-migration-20261006/source-retirement-execution'),
             'packet_sha256': PACKET, 'allowlist_sha256': digest(allowlist), 'evidence_commit': 'a'*40,
             'root_allowlist_path': 'docs/aws-migration-2026-10-06/archive-source-retirement-allowlist.json',
             'principals': PRINCIPALS, 'source': BUCKET, 'destination': TARGET,
             'issued_at': '2026-10-07T12:00:00Z', 'expires_at': '2026-10-07T12:30:00Z',
             'code_sha256': {'fixture': 'code'}, 'evidence': pins,
             'preserve_keys_catalogs_local_source': True, 'shared_principals_roles_retained': True}
        for field in ['source_configuration_sha256', 'destination_configuration_sha256',
                      'version_metadata_sha256', 'permission_proof_sha256', 'hash_reuse_scope_sha256']:
            g[field] = 'b'*64
        return g, allowlist, blobs

    def gate_load(self, g, allowlist, blobs, now=1791375000):
        raw = encoded(g)
        return load_gate(raw, digest(raw), allowlist, lambda commit, path: blobs[path],
                         lambda: {'fixture': 'code'}, lambda: now)

    def test_valid_gate_reads_committed_root_scope(self):
        g, a, b = self.gate_fixture()
        # Timestamp derived to avoid a date arithmetic fixture mistake.
        self.assertEqual(self.gate_load(g, a, b, timestamp('2026-10-07T12:15:00Z'))['decision'], 'ACCEPT')

    def test_root_true_flags_without_underlying_proofs_fail(self):
        g, a, b = self.gate_fixture()
        pin = g['evidence'][0]
        e = json.loads(b[pin['path']]); e['underlying_proofs'] = []
        b[pin['path']] = encoded(e); pin['sha256'] = digest(b[pin['path']])
        with self.assertRaisesRegex(Stop, 'SUBSTANTIVE_ROOT_ATTESTATION_REQUIRED'):
            self.gate_load(g, a, b, timestamp('2026-10-07T12:15:00Z'))

    def test_distinct_root_allowlist_required(self):
        g, a, b = self.gate_fixture()
        b[g['root_allowlist_path']] = a + b' '
        with self.assertRaisesRegex(Stop, 'DISTINCT_COMMITTED_ROOT_ALLOWLIST_REQUIRED'):
            self.gate_load(g, a, b, timestamp('2026-10-07T12:15:00Z'))

    def test_expiry_during_committed_evidence_read(self):
        g, a, b = self.gate_fixture(); raw = encoded(g)
        times = [timestamp('2026-10-07T12:15:00Z')]
        def read(commit, path):
            times[0] = timestamp('2026-10-07T12:31:00Z')
            return b[path]
        with self.assertRaisesRegex(Stop, 'ROOT_GATE_EXPIRED'):
            load_gate(raw, digest(raw), a, read, lambda: {'fixture': 'code'}, lambda: times[0])

    def test_stale_root_evidence_rejected(self):
        g, a, b = self.gate_fixture(); pin = g['evidence'][0]
        e = json.loads(b[pin['path']]); e['valid_until'] = '2026-10-07T12:10:00Z'
        b[pin['path']] = encoded(e); pin['sha256'] = digest(b[pin['path']])
        with self.assertRaisesRegex(Stop, 'EVIDENCE_FRESHNESS'):
            self.gate_load(g, a, b, timestamp('2026-10-07T12:15:00Z'))

    def test_torn_state_preserved(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'journal'
            p.write_bytes(b'{torn')
            with self.assertRaisesRegex(Stop, 'TORN_JOURNAL'):
                Journal(p, 'gate', 'allowlist')
            self.assertEqual(p.read_bytes(), b'{torn')

    def test_hash_chain_and_gate_mismatch(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/'journal'
            Journal(p, 'gate', 'allowlist').append('intent', 'bucket', BUCKET)
            with self.assertRaisesRegex(Stop, 'JOURNAL_BINDING_OR_CHAIN'):
                Journal(p, 'new-gate', 'allowlist')
            raw = p.read_bytes().replace(b'"sequence":0', b'"sequence":1')
            p.write_bytes(raw)
            with self.assertRaisesRegex(Stop, 'JOURNAL_BINDING_OR_CHAIN'):
                Journal(p, 'gate', 'allowlist')

    def test_lock_second_writer_and_stale_lock_preserved(self):
        with tempfile.TemporaryDirectory() as d:
            with execution_lock(d):
                with self.assertRaises(FileExistsError):
                    with execution_lock(d):
                        self.fail('second writer')
                self.assertTrue((Path(d)/'execution.lock').exists())

    def test_noninjective_mapping(self):
        a = copy.deepcopy(REAL)
        a['rows'][1]['key'] = a['rows'][0]['key']
        a['rows'][1]['destination_version'] = a['rows'][0]['destination_version']
        with self.assertRaisesRegex(Stop, 'NONINJECTIVE_MAPPING'):
            validate_allowlist(a)

    def test_full_count_bytes_exact(self):
        a = copy.deepcopy(REAL)
        a['rows'][0]['bytes'] += 1
        with self.assertRaisesRegex(Stop, 'FULL205_SCOPE'):
            validate_allowlist(a)

    def test_owner_mismatch(self):
        with self.assertRaisesRegex(Stop, 'VERSION_OWNER'):
            compare_inventory({'rows': [{'key': 'k', 'version': 'v', 'bytes': 1, 'owner': 'other'}],
                               'markers': [], 'uploads': []},
                              [{'key': 'k', 'source_version': 'v', 'bytes': 1}], 'source_version', 'owner')

    def test_observed_full_metadata_comparator_negative_fields(self):
        # Metadata-only receipt: no payload, key or live service call.
        x = json.loads((Path(__file__).parent/'evidence/current-metadata-observation.json').read_bytes())
        compare_version_metadata(REAL, x['version_metadata'], x['configuration'])
        for field in ('ContentType', 'Metadata', 'WebsiteRedirectLocation', 'Expires', 'ObjectLockMode'):
            with self.subTest(field=field):
                changed = copy.deepcopy(x['version_metadata'])
                changed[0]['head'][field] = {'altered': 'yes'} if field == 'Metadata' else 'altered'
                with self.assertRaisesRegex(Stop, 'HEADER_PRESERVATION'):
                    compare_version_metadata(REAL, changed, x['configuration'])
        changed = copy.deepcopy(x['version_metadata']); changed[0]['tags'] = [{'Key': 'new', 'Value': 'tag'}]
        with self.assertRaisesRegex(Stop, 'TAG_PRESERVATION'):
            compare_version_metadata(REAL, changed, x['configuration'])
        changed = copy.deepcopy(x['version_metadata']); changed[0]['acl']['Grants'].append({'Permission': 'READ'})
        with self.assertRaisesRegex(Stop, 'OBJECT_PRIVATE_OWNER_ACL'):
            compare_version_metadata(REAL, changed, x['configuration'])

    def test_pagination_missing_version_marker(self):
        class Client:
            def list_object_versions(self, **args):
                self.args = args
                return {'Name': BUCKET, 'IsTruncated': True, 'NextKeyMarker': 'k'}
        c = Client()
        with self.assertRaisesRegex(Stop, 'VERSION_PAGINATION'):
            full_inventory(c, BUCKET, SOURCE)
        self.assertNotIn('Prefix', c.args)
        self.assertEqual(c.args['ExpectedBucketOwner'], SOURCE)

    def test_pagination_repeat_blocks(self):
        class Client:
            def list_object_versions(self, **args):
                return {'Name': BUCKET, 'IsTruncated': True, 'NextKeyMarker': 'k', 'NextVersionIdMarker': 'v'}
        with self.assertRaisesRegex(Stop, 'VERSION_PAGINATION'):
            full_inventory(Client(), BUCKET, SOURCE)

    def test_disabled_root_gate_before_evidence(self):
        raw = encoded({'type': 'archive-retirement-root-gate-v1', 'authorized': False})
        with self.assertRaisesRegex(Stop, 'ROOT_GATE_DISABLED'):
            load_gate(raw, digest(raw), encoded(REAL), lambda *a: self.fail('evidence read'), lambda: {})

    def test_execute_cli_disabled_before_aws(self):
        import cli
        with patch.object(sys, 'argv', ['cli.py', 'execute']):
            with self.assertRaisesRegex(Stop, 'ROOT_GATE_DISABLED'):
                cli.main()


if __name__ == '__main__':
    unittest.main(verbosity=2)
