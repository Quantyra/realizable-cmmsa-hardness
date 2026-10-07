"""Synthetic full205 production integration with Git blobs and real SDK endpoints."""
import copy
import json
import os
import socket
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime, timezone, timedelta
from pathlib import Path
from unittest.mock import patch
from urllib.parse import urlparse, parse_qs, unquote
sys.path.insert(0, str(Path(__file__).resolve().parent))
import boto3
from botocore.awsrequest import AWSResponse
from botocore.exceptions import ClientError, ReadTimeoutError
from safety import *
from root import RootLoader, PROOF_TYPES, KIND_PROOFS, ROOT_GATE_PATH, SUPPLEMENT, pins
from adapter import ProductionAdapter
from policy import source_freeze, destination_custody
from permission import evaluate, simulate_one
from retirement import run
from aws import Mutator
from test_transport import Raw

HERE = Path(__file__).resolve().parent
A = json.loads((HERE/'evidence/bound-allowlist.json').read_bytes())
PREFIX = 'docs/aws-migration-2026-10-06/'


def api_error(code):
    return ClientError({'Error': {'Code': code}, 'ResponseMetadata': {'HTTPStatusCode': 404}}, 'Synthetic')


class IAM:
    def __init__(self):
        self.calls = []
        self.deny = False
        self.truncate = False
        self.omit = False

    def simulate_principal_policy(self, **kw):
        self.calls.append(kw)
        assert kw['PolicySourceArn'] == kw['CallerArn'] == PRINCIPALS[SOURCE]
        assert kw['ResourceOwner'] == f'arn:aws:iam::{SOURCE}:root' and len(kw['ResourceArns']) == 1
        action, resource = kw['ActionNames'][0], kw['ResourceArns'][0]
        decision = 'explicitDeny' if self.deny or action == 's3:PutObject' else 'allowed'
        resource_rows = [] if self.omit else [{'EvalResourceName': resource, 'EvalResourceDecision': decision}]
        return {'IsTruncated': self.truncate, 'EvaluationResults': [{'EvalActionName': action,
                'EvalResourceName': resource, 'EvalDecision': decision, 'ResourceSpecificResults': resource_rows}],
                'ResponseMetadata': {'RequestId': 'synthetic-iam-request'}}


class S3:
    def __init__(self, account, baseline):
        self.account = account
        self.bucket = BUCKET if account == SOURCE else TARGET
        self.config = copy.deepcopy(baseline['configuration'][account])
        self.inv = copy.deepcopy(baseline['inventories'][account])
        self.md = {(x['key'], x['version']): copy.deepcopy(x) for x in baseline['version_metadata']
                   if x['bucket'] == self.bucket}
        self.absent = False

    def args(self, kw):
        assert kw['Bucket'] == self.bucket and kw['ExpectedBucketOwner'] == self.account
        if self.absent:
            raise api_error('NoSuchBucket')

    def list_object_versions(self, **kw):
        self.args(kw); assert 'Prefix' not in kw
        return {'Name': self.bucket, 'IsTruncated': False,
                'Versions': [{'Key': r['key'], 'VersionId': r['version'], 'Size': r['bytes'],
                              'ETag': r['etag'], 'IsLatest': r['is_latest'],
                              'LastModified': datetime.fromisoformat(r['last_modified']),
                              'Owner': {'ID': r['owner']}, 'StorageClass': r['storage_class']}
                             for r in self.inv['rows']], 'DeleteMarkers': self.inv['markers']}

    def list_multipart_uploads(self, **kw):
        self.args(kw)
        return {'Bucket': self.bucket, 'IsTruncated': False, 'Uploads': []}

    def head_object(self, **kw):
        self.args(kw)
        return copy.deepcopy(self.md[(kw['Key'], kw['VersionId'])]['head'])

    def get_object_tagging(self, **kw):
        self.args(kw)
        return {'VersionId': kw['VersionId'], 'TagSet': self.md[(kw['Key'], kw['VersionId'])]['tags']}

    def get_object_acl(self, **kw):
        self.args(kw)
        return self.md[(kw['Key'], kw['VersionId'])]['acl']

    def __getattr__(self, name):
        if name not in self.config:
            raise AssertionError('Unexpected API: ' + name)
        def read(**kw):
            self.args(kw)
            r = self.config[name]
            if r.get('absent'):
                raise api_error(r['code'])
            return copy.deepcopy(r)
        return read


class FakeAWS:
    def __init__(self, baseline):
        self.iam = IAM()
        self.s3 = {a: S3(a, baseline) for a in (SOURCE, DEST)}
        self.ident = PRINCIPALS.copy()
        self.sessions = {SOURCE: boto3.Session(aws_access_key_id='SYNTHETIC',
                        aws_secret_access_key='SYNTHETIC', region_name='us-east-1')}

    def client(self, service, account):
        if service == 'iam':
            assert account == SOURCE
            return self.iam
        assert service == 's3'
        return self.s3[account]

    def identity(self, account):
        require(self.ident[account] == PRINCIPALS[account], 'PRINCIPAL_DRIFT')
        return self.ident[account]


def git(repo, *args):
    r = subprocess.run(['git', *args], cwd=repo, capture_output=True)
    if r.returncode:
        raise AssertionError('Synthetic Git command failed')
    return r.stdout.decode().strip()


class Bundle:
    def __init__(self, directory, change=None):
        self.repo = Path(directory)/'root'; self.repo.mkdir()
        git(self.repo, 'init', '-q')
        git(self.repo, 'config', 'user.email', 'fixture@example.invalid')
        git(self.repo, 'config', 'user.name', 'Synthetic independent root')
        self.base = json.loads((HERE/'evidence/current-metadata-observation.json').read_bytes())
        for account, policy in [(SOURCE, source_freeze()), (DEST, destination_custody())]:
            self.base['configuration'][account]['get_bucket_policy']['Policy'] = json.dumps(policy, separators=(',', ':'))
        now = datetime.now(timezone.utc) - timedelta(seconds=1)
        self.issued, self.expires = now.isoformat(), (now + timedelta(hours=1)).isoformat()
        common = {'packet_sha256': PACKET, 'allowlist_sha256': digest((HERE/'evidence/bound-allowlist.json').read_bytes()),
                  'reviewer_role': 'root-independent-verifier', 'observed_at': self.issued, 'valid_until': self.expires}
        self.proofs = {name: {'type': t, **common} for name, t in PROOF_TYPES.items()}
        self.proofs['baseline'] = self.base
        self.proofs['hash_scope'].update(versions=205, encrypted_chunks=105, recovery_catalogs=44,
            authentication_proof_sha256='a'*64, version_metadata_sha256=digest(self.base['version_metadata']),
            scope={'packet_sha256': PACKET, 'source': BUCKET, 'destination': TARGET, 'rows': A['rows'],
                   'catalogs': A['catalogs'], 'packet_artifacts': A['packet_artifacts']})
        permission, _ = evaluate(IAM(), A, source_freeze())
        self.proofs['permission']['proof'] = permission
        for name, bucket, policy in [('source_freeze', BUCKET, source_freeze()), ('destination_custody', TARGET, destination_custody())]:
            self.proofs[name].update(bucket=bucket, policy=policy, policy_sha256=digest(policy),
                                    readback_request_id='synthetic-readback', control_custodians=['synthetic-root'], maintenance_until=self.expires)
        self.proofs['destination_custody'].update(versions=A['rows'], catalogs=A['catalogs'],
            key_custody_receipts=[{'custodian': 'synthetic-root', 'key_reference': 'symbolic-only',
                                  'receipt_sha256': 'a'*64, 'source_required': False}])
        self.proofs['producer_shutdown'].update(bucket=BUCKET, topology_receipts=['synthetic-topology'],
            unresolved_producers=[], producers=[{'id': 'synthetic-producer', 'kind': 'remote-fixture',
            'shutdown_receipt_sha256': 'a'*64, 'probe': {'kind': 'root-observed-remote-stop', 'operator': 'synthetic',
            'service_or_host': 'fixture.invalid', 'stop_command': 'synthetic-stop', 'observed_state': 'stopped', 'receipt_sha256': 'a'*64}}])
        self.proofs['archive_acceptance'].update(decision='ACCEPT', https_supplement_sha256=SUPPLEMENT,
            catalogs=A['catalogs'], versions=205, encrypted_chunks=105, authentication_proof_sha256='a'*64)
        self.proofs['consumer'].update(account=DEST, principal=PRINCIPALS[DEST], bucket=TARGET, catalogs=A['catalogs'],
            actual_command='synthetic-restore', installed_config_sha256='a'*64, exit_code=0,
            restored_bytes=1, restored_sha256='a'*64, exact_versions=[{'key': A['rows'][0]['key'],
            'version': A['rows'][0]['destination_version']}], source_required=False)
        self.proofs['website'].update(account=DEST, authoritative_nameservers=['ns.fixture.invalid'],
            delegation_observed=['ns.fixture.invalid'], complete_dns_inventory_sha256='a'*64,
            tls_fingerprints=['synthetic'], deployment_command='synthetic-deploy', source_required=False,
            routes=[{'url': 'https://fixture.invalid/', 'status': 200, 'response_sha256': 'a'*64}])
        self.proofs['ownership'].update(bucket=BUCKET, versions=A['rows'], attribution_receipts=['synthetic'],
            unresolved_bucket_data=[], retained_shared_principals=[PRINCIPALS[SOURCE]], other_buckets_in_scope=[])
        self.proofs['dependencies'].update(bucket=BUCKET, examined_surfaces=['fixture'], unresolved_for_bucket=[],
            findings=[{'surface': 'fixture', 'disposition': 'destination-consumer', 'receipt_sha256': 'a'*64}])
        self.proofs['code_review'].update(decision='GO-WITH-BOUNDARIES', reviewer_role='independent-retirement-code-reviewer',
            code_sha256=pins(), botocore='1.43.108', boto3='1.43.108', transport_receipt_sha256='a'*64, findings=['synthetic only'])
        receipt = {'path': PREFIX + 'fixture-raw-receipt.json', 'sha256': digest(encoded({'synthetic_receipt': True}))}
        self.write(receipt['path'], encoded({'synthetic_receipt': True}))
        self.proofs['hash_scope']['authentication_proof_sha256'] = receipt['sha256']
        self.proofs['archive_acceptance']['authentication_proof_sha256'] = receipt['sha256']
        self.proofs['destination_custody']['key_custody_receipts'][0]['receipt_sha256'] = receipt['sha256']
        self.proofs['producer_shutdown']['topology_receipts'] = [receipt]
        self.proofs['producer_shutdown']['producers'][0]['shutdown_receipt_sha256'] = receipt['sha256']
        self.proofs['producer_shutdown']['producers'][0]['probe']['receipt_sha256'] = receipt['sha256']
        self.proofs['website']['complete_dns_inventory_sha256'] = receipt['sha256']
        self.proofs['website']['tls_fingerprints'] = ['a'*64]
        self.proofs['ownership']['attribution_receipts'] = [receipt]
        self.proofs['dependencies']['findings'][0]['receipt_sha256'] = receipt['sha256']
        self.proofs['code_review']['transport_receipt_sha256'] = receipt['sha256']
        if change:
            change(self.proofs)
        pointers = {}
        for name, p in self.proofs.items():
            path = PREFIX + 'fixture-' + name + '.json'; self.write(path, encoded(p))
            pointers[name] = {'path': path, 'sha256': digest(encoded(p))}
        evidence = []
        for kind, names in KIND_PROOFS.items():
            att = {'type': 'archive-retirement-attestation-v1', 'kind': kind, 'decision': 'ACCEPT', **common,
                   'underlying_proofs': [pointers[name] for name in sorted(names)] + [receipt]}
            path = PREFIX + 'fixture-accept-' + kind + '.json'; self.write(path, encoded(att))
            evidence.append({'kind': kind, 'path': path, 'sha256': digest(encoded(att))})
        self.write(PREFIX + 'archive-source-retirement-allowlist.json', (HERE/'evidence/bound-allowlist.json').read_bytes())
        git(self.repo, 'add', '.'); git(self.repo, 'commit', '-qm', 'Synthetic independent operating proofs')
        self.commit = git(self.repo, 'rev-parse', 'HEAD')
        self.g = {'type': 'archive-retirement-root-gate-v1', 'authorized': True, 'execution_cli_enabled': True,
            'decision': 'ACCEPT', 'evidence_commit': self.commit, 'packet_sha256': PACKET,
            'allowlist_sha256': common['allowlist_sha256'], 'root_allowlist_path': PREFIX + 'archive-source-retirement-allowlist.json',
            'source': BUCKET, 'destination': TARGET, 'principals': PRINCIPALS,
            'execution_state_directory': str(Path.home()/'.quantyra/aws-migration-20261006/source-retirement-execution'),
            'issued_at': self.issued, 'expires_at': self.expires, 'code_sha256': pins(), 'evidence': evidence,
            'production_proofs': pointers, 'preserve_keys_catalogs_local_source': True, 'shared_principals_roles_retained': True,
            'source_configuration_sha256': digest(self.base['configuration'][SOURCE]),
            'destination_configuration_sha256': digest(self.base['configuration'][DEST]),
            'version_metadata_sha256': digest(self.base['version_metadata']), 'permission_proof_sha256': digest(permission),
            'hash_reuse_scope_sha256': digest(self.proofs['hash_scope'])}
        self.gate = self.repo/ROOT_GATE_PATH; self.write(ROOT_GATE_PATH, encoded(self.g))
        git(self.repo, 'add', '.'); git(self.repo, 'commit', '-qm', 'Synthetic separate gate commit')
        self.gate_commit = git(self.repo, 'rev-parse', 'HEAD')
        self.hash = digest(self.gate.read_bytes())

    def write(self, path, data):
        p = self.repo/path; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(data)

    def loader(self):
        return RootLoader(self.gate, self.hash, self.commit, self.gate_commit, self.repo)


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        self.artifact_impl = ProductionAdapter.verify_packet_artifacts
        # Synthetic endpoint scenarios isolate bulk artifact hashing, which has
        # its own real all305 --verify-only check and corruption/path regressions.
        artifact_patch = patch.object(ProductionAdapter, 'verify_packet_artifacts', return_value=None)
        artifact_patch.start(); self.addCleanup(artifact_patch.stop)
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.bundle = Bundle(self.temp.name)
        self.root = self.bundle.loader()
        self.aws = FakeAWS(self.bundle.base)
        self.adapter = ProductionAdapter(self.aws, self.root, True)
        self.sends = []
        self.wire_mode = 'success'
        # Production lock path is validated by RootLoader; only the synthetic
        # execution's lock/journal uses an injected temporary test state directory.
        self.state = Path(self.temp.name)/'state'; self.state.mkdir()
        self.journal = Journal(self.state/'retirement.journal', self.root.expected_hash, digest(self.root.allowlist_bytes))

    def authorize(self):
        g = self.root.authorize(); g['execution_state_directory'] = str(self.state); return g

    def wire(self, request):
        self.sends.append(request)
        assert request.headers['x-amz-expected-bucket-owner'] == SOURCE.encode()
        u = urlparse(request.url); version = parse_qs(u.query).get('versionId', [None])[0]
        key = unquote(u.path.lstrip('/'))
        source = self.aws.s3[SOURCE]
        if self.wire_mode == 'ambiguous':
            return AWSResponse(request.url, 503, {'content-type': 'application/xml'}, Raw(b'<Error><Code>ServiceUnavailable</Code></Error>'))
        if version:
            assert request.headers['If-Match'] == next(r['source_etag'].encode() for r in A['rows'] if r['source_version'] == version)
            source.inv['rows'] = [r for r in source.inv['rows'] if (r['key'], r['version']) != (key, version)]
        else:
            assert not source.inv['rows']; source.absent = True
        if self.wire_mode == 'lost':
            raise ReadTimeoutError(endpoint_url='https://fixture.invalid')
        return AWSResponse(request.url, 204, {'x-amz-version-id': version or '', 'x-amz-request-id': 'synthetic-delete'}, Raw(b''))

    def execute(self):
        mutator = Mutator(self.aws.sessions[SOURCE], self.root.authorize)
        mutator.client._endpoint.http_session.send = self.wire
        self.adapter.mutator = mutator
        with patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
            return run(self.adapter, A, self.authorize, self.journal, True)

    def prior_version_deletions(self):
        for row in A['rows']:
            identity = [row['key'], row['source_version']]
            self.journal.append('intent', 'version', identity, destination_version=row['destination_version'])
            self.journal.append('confirmed', 'version', identity, observed_absent=True)
        self.aws.s3[SOURCE].inv['rows'] = []

    def test_real_adapter_full205_endpoint_success(self):
        result = self.execute()
        self.assertEqual(len(self.sends), 206)
        self.assertEqual(result['observation']['destination_versions'], 205)
        self.assertTrue(self.aws.s3[SOURCE].absent)
        self.assertEqual(len(self.aws.s3[DEST].inv['rows']), 205)

    def test_root_check_uses_permissions_no_writes(self):
        self.adapter.execute = False
        with patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
            result = run(self.adapter, A, self.authorize)
        self.assertTrue(result['permissions_checked']); self.assertEqual(self.sends, [])
        self.assertGreaterEqual(len(self.aws.iam.calls), 412)

    def test_ambiguous_real_endpoint_no_retry_on_restart(self):
        self.wire_mode = 'ambiguous'
        for _ in range(2):
            with self.assertRaisesRegex(Stop, 'AMBIGUOUS_VERSION_DELETE_NO_RETRY'):
                self.execute()
        self.assertEqual(len(self.sends), 1)

    def test_lost_reply_real_endpoint_observed_absence(self):
        self.wire_mode = 'lost'; self.execute()
        self.assertEqual(len(self.sends), 206)
        self.assertTrue(any(e['details'].get('lost_reply') for e in self.journal.events))

    def test_recreated_empty_bucket_after_complete(self):
        self.prior_version_deletions()
        self.execute(); self.aws.s3[SOURCE].absent = False
        with self.assertRaisesRegex(Stop, 'BUCKET_REAPPEARANCE'):
            self.execute()
        self.assertEqual(len(self.sends), 1)

    def test_destination_loss_after_last_dependency(self):
        self.prior_version_deletions()
        original = self.adapter.dependencies
        def late():
            original()
            if self.aws.s3[SOURCE].absent:
                self.aws.s3[DEST].inv['rows'].pop()
        self.adapter.dependencies = late
        with self.assertRaisesRegex(Stop, 'DESTINATION_CUSTODY_LOST'):
            self.execute()
        self.assertFalse(any(e['kind'] == 'terminal' for e in self.journal.events))

    def test_denied_real_simulation_check_only(self):
        self.aws.iam.deny = True
        with self.assertRaisesRegex(Stop, 'PERMISSION_DENIED'):
            run(self.adapter, A, self.authorize)
        self.assertEqual(self.sends, [])

    def test_metadata_drift_actual_adapter(self):
        row = A['rows'][0]
        self.aws.s3[DEST].md[(row['key'], row['destination_version'])]['tags'].append({'Key': 'drift', 'Value': 'x'})
        with self.assertRaisesRegex(Stop, 'CURRENT_EXACT_VERSION_METADATA_DRIFT'):
            run(self.adapter, A, self.authorize)

    def test_mutable_gate_not_committed_bytes(self):
        self.bundle.gate.write_bytes(self.bundle.gate.read_bytes() + b' ')
        with self.assertRaisesRegex(Stop, 'COMMITTED_ROOT_GATE_REQUIRED'):
            self.root.authorize()

    def test_source_put_global_denied_has_no_executor_exception(self):
        stmt = source_freeze()['Statement'][1]
        self.assertEqual(stmt['Principal'], '*'); self.assertNotIn('Condition', stmt)
        self.assertIn('s3:PutObject', stmt['Action'])

    def test_root_flags_without_real_producer_contract_block(self):
        d = Path(self.temp.name)/'negative'; d.mkdir()
        b = Bundle(d, lambda p: p['producer_shutdown'].update(producers=[]))
        with self.assertRaisesRegex(Stop, 'ACTUAL_PRODUCER_SHUTDOWN_REQUIRED'):
            b.loader()

    def test_uncommitted_shutdown_receipt_hash_blocks(self):
        d = Path(self.temp.name)/'negative'; d.mkdir()
        b = Bundle(d, lambda p: p['producer_shutdown']['producers'][0]['probe'].update(receipt_sha256='b'*64))
        with self.assertRaisesRegex(Stop, 'REMOTE_STOP_RECEIPT_REQUIRED'):
            b.loader()

    def test_permission_truncation_and_resource_omission(self):
        for field, code in [('truncate', 'PERMISSION_TRUNCATED'), ('omit', 'PERMISSION_RESOURCE_COVERAGE')]:
            with self.subTest(field=field):
                iam = IAM(); setattr(iam, field, True)
                with self.assertRaisesRegex(Stop, code):
                    simulate_one(iam, 's3:DeleteBucket', f'arn:aws:s3:::{BUCKET}', source_freeze())

    def test_policy_drift_before_target_simulation_blocks(self):
        self.aws.s3[SOURCE].config['get_bucket_policy']['Policy'] = json.dumps({'Version': '2012-10-17', 'Statement': []})
        with self.assertRaisesRegex(Stop, 'SIMULATION_CURRENT_POLICY_DRIFT'):
            self.adapter.focused_permissions(A['rows'][0])
        self.assertEqual(self.sends, [])

    def test_current_pid_readonly_probe_reports_live(self):
        from process_probe import process_absent
        self.assertFalse(process_absent(os.getpid()))

    def test_original_allowlist_cannot_be_rebound_by_root(self):
        from root import GitEvidence
        original = GitEvidence.read
        def altered(reader, commit, path):
            result = original(reader, commit, path)
            return result + b' ' if path.endswith('archive-source-retirement-allowlist.json') else result
        with patch.object(GitEvidence, 'read', altered):
            with self.assertRaisesRegex(Stop, 'ORIGINAL_FULL205_ALLOWLIST_CHANGED'):
                self.bundle.loader()

    def test_state_symlink_refused_before_journal_read(self):
        with patch.object(Path, 'is_symlink', return_value=True):
            with self.assertRaisesRegex(Stop, 'STATE_REPARSE_POINT_REFUSED'):
                Journal(self.state/'untrusted', self.root.expected_hash, 'allowlist')

    def test_artifact_checker_rejects_unsafe_path(self):
        # Call the original implementation despite the scenario-suite hash seam.
        from adapter import ProductionAdapter
        with patch.object(ProductionAdapter, 'verify_packet_artifacts', self.artifact_impl):
            self.adapter.a = {'packet_artifacts': [{'file': str(Path(self.temp.name)/'unowned.key'), 'sha256': 'a'*64}]}
            with self.assertRaisesRegex(Stop, 'UNSAFE_PACKET_ARTIFACT'):
                self.adapter.verify_packet_artifacts()

    def test_closing_namespace_relist_catches_reappearance(self):
        self.prior_version_deletions()
        original_metadata = self.adapter.metadata
        def late(row, present):
            original_metadata(row, present)
            if self.aws.s3[SOURCE].absent:
                self.aws.s3[SOURCE].absent = False
        self.adapter.metadata = late
        with self.assertRaisesRegex(Stop, 'SOURCE_CHANGED_DURING_CLOSING_METADATA'):
            self.execute()
        self.assertFalse(any(e['kind'] == 'terminal' for e in self.journal.events))

    def test_expiry_at_actual_endpoint_zero_sends(self):
        calls = []
        def auth():
            calls.append(1)
            if len(calls) == 2:
                raise Stop('ROOT_GATE_EXPIRED')
        mutator = Mutator(self.aws.sessions[SOURCE], auth)
        mutator.client._endpoint.http_session.send = self.wire
        with patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
            with self.assertRaisesRegex(Stop, 'ROOT_GATE_EXPIRED'):
                mutator.delete_version(A['rows'][0])
        self.assertEqual(self.sends, [])

    def test_cli_execute_reaches_production_adapter_under_valid_root(self):
        import cli
        self.prior_version_deletions()
        output = self.state/'synthetic-cli-result.json'
        real_loader = self.root
        # Route the actual CLI through a prevalidated synthetic root and the actual
        # production adapter; no source/destination SDK sockets can be created.
        original_auth = real_loader.authorize
        def cli_auth():
            g = original_auth(); g['execution_state_directory'] = str(self.state); return g
        real_loader.authorize = cli_auth
        original_init = ProductionAdapter.__init__
        def setup(adapter, aws, root, execute=False):
            original_init(adapter, aws, root, execute)
            mutator = Mutator(aws.sessions[SOURCE], root.authorize)
            mutator.client._endpoint.http_session.send = self.wire
            adapter.mutator = mutator
        argv = ['cli.py', 'execute', '--gate', str(self.bundle.gate), '--gate-sha256', self.bundle.hash,
                '--root-commit', self.bundle.commit, '--gate-commit', self.bundle.gate_commit, '--output', str(output)]
        with patch.object(sys, 'argv', argv), patch.object(cli, 'RootLoader', return_value=real_loader), \
             patch('aws.AWS', return_value=self.aws), patch.object(ProductionAdapter, '__init__', setup), \
             patch.object(socket, 'socket', side_effect=AssertionError('REAL_SOCKET_FORBIDDEN')):
            cli.main()
        self.assertTrue(output.exists()); self.assertEqual(len(self.sends), 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
