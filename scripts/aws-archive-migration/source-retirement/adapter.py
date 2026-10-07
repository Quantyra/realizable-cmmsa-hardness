"""Production adapter: fresh S3/STS/IAM metadata, no payload/secret/key API."""
import copy
import json
import socket
from pathlib import Path
from safety import *
from inventory import configuration, full_inventory, version_metadata
from policy import source_freeze, destination_custody, policy_value
from permission import evaluate, require_allowed, simulate_one
from aws import Mutator
from process_probe import process_absent


class ProductionAdapter:
    def __init__(self, aws, root, execute=False):
        self.aws, self.root, self.execute = aws, root, execute
        self.a = root.allowlist
        self.proofs = root.proofs
        self.baseline = self.proofs['baseline']
        self.expected_metadata = {(m['bucket'], m['key'], m['version']): m
                                  for m in self.baseline['version_metadata']}
        self.mutator = None
        self.last_permission = None

    def identities(self):
        return {a: self.aws.identity(a) for a in (SOURCE, DEST)}

    def configuration(self, account):
        bucket = BUCKET if account == SOURCE else TARGET
        try:
            c = configuration(self.aws.client('s3', account), bucket, account)
        except Exception as e:
            if account == SOURCE and getattr(e, 'response', {}).get('Error', {}).get('Code') == 'NoSuchBucket':
                return None
            raise
        require(policy_value(c) == (source_freeze() if account == SOURCE else destination_custody()),
                'ACTUAL_FREEZE_OR_DESTINATION_HOLD_MISSING')
        return c

    def _state(self, account, bucket):
        try:
            inv = full_inventory(self.aws.client('s3', account), bucket, account)
        except Exception as e:
            if account == SOURCE and getattr(e, 'response', {}).get('Error', {}).get('Code') == 'NoSuchBucket':
                return None
            raise
        owner = self.baseline['configuration'][account]['get_bucket_acl']['Owner']['ID']
        require(all(r['owner'] == owner for r in inv['rows']), 'CURRENT_VERSION_OWNER')
        return inv

    def source_state(self):
        return self._state(SOURCE, BUCKET)

    def destination_state(self):
        return self._state(DEST, TARGET)

    def metadata(self, row, source_present):
        for account, bucket, field in [(SOURCE, BUCKET, 'source_version'), (DEST, TARGET, 'destination_version')]:
            if account == SOURCE and not source_present:
                continue
            actual = version_metadata(self.aws.client('s3', account), bucket, account, row['key'], row[field])
            expected = self.expected_metadata[(bucket, row['key'], row[field])]
            require(digest(actual) == digest(expected), 'CURRENT_EXACT_VERSION_METADATA_DRIFT')

    def hash_scope(self):
        return self.proofs['hash_scope']

    def permissions(self):
        require(self.aws.identity(SOURCE) == PRINCIPALS[SOURCE], 'SIMULATION_PRINCIPAL_DRIFT')
        policy = source_freeze()
        c = self.configuration(SOURCE)
        if c is not None:
            require(policy_value(c) == policy, 'SIMULATION_CURRENT_POLICY_DRIFT')
        proof, observations = evaluate(self.aws.client('iam', SOURCE), self.a, policy)
        self.last_permission = observations
        return require_allowed(proof, self.a)

    def focused_permissions(self, row):
        # Current target permission is newly simulated; the full proof is refreshed
        # at preflight and final closure. No cached permission authorizes a mutation.
        require(self.aws.identity(SOURCE) == PRINCIPALS[SOURCE], 'SIMULATION_PRINCIPAL_DRIFT')
        accepted = copy.deepcopy(self.proofs['permission']['proof'])
        current_policy = json.loads(self.aws.client('s3', SOURCE).get_bucket_policy(
            Bucket=BUCKET, ExpectedBucketOwner=SOURCE)['Policy'])
        require(current_policy == source_freeze(), 'SIMULATION_CURRENT_POLICY_DRIFT')
        if row == 'bucket':
            index, action, resource, version = -1, 's3:DeleteBucket', f'arn:aws:s3:::{BUCKET}', None
        else:
            require(row in self.a['rows'], 'MUTATION_ALLOWLIST_SCOPE')
            index = self.a['rows'].index(row)
            action, resource, version = 's3:DeleteObjectVersion', f'arn:aws:s3:::{BUCKET}/{row["key"]}', row['source_version']
        actual = simulate_one(self.aws.client('iam', SOURCE), action, resource, current_policy, version)
        stable = {k: v for k, v in actual.items() if k != 'request_id'}
        require(stable == accepted['version_evaluations'][index] and actual['decision'] == 'allowed',
                'FRESH_TARGET_PERMISSION_DRIFT')
        return require_allowed(accepted, self.a)

    def dependencies(self):
        self.root.authorize()
        self.verify_packet_artifacts()
        for producer in self.proofs['producer_shutdown']['producers']:
            probe = producer['probe']
            if probe['kind'] == 'local-pid-absent':
                require(probe['host'].casefold() == socket.gethostname().casefold(), 'PRODUCER_HOST_SCOPE')
                require(process_absent(probe['pid']), 'SOURCE_PRODUCER_STILL_RUNNING')
            require(probe.get('observed_state', 'stopped') == 'stopped', 'REMOTE_PRODUCER_NOT_STOPPED')
        self.root.authorize()

    def verify_packet_artifacts(self):
        # Recheck exact local immutable migration artifacts, without key/catalog
        # decoding. Hash reuse is independent acceptance under exact full scope.
        permitted = [Path.home()/'.quantyra/aws-migration-20261006',
                     Path.home()/'.quantyra/archive-catalogs', Path(__file__).resolve().parent.parent]
        for pin in self.a['packet_artifacts']:
            file = Path(pin['file']).resolve()
            require(any(file.is_relative_to(p.resolve()) for p in permitted) and
                    file.suffix != '.key' and 'credentials' not in str(file).lower(), 'UNSAFE_PACKET_ARTIFACT')
            import hashlib
            h = hashlib.sha256()
            with file.open('rb') as f:
                for chunk in iter(lambda: f.read(1024 * 1024), b''):
                    h.update(chunk)
            require(h.hexdigest() == pin['sha256'], 'PRESERVED_PACKET_ARTIFACT_DRIFT')

    def _mutator(self, row):
        require(self.execute, 'CHECK_ONLY_MUTATION_REFUSED')
        self.root.authorize()
        self.focused_permissions(row)
        require(self.aws.identity(SOURCE) == PRINCIPALS[SOURCE], 'MUTATION_PRINCIPAL_DRIFT')
        if self.mutator is None:
            self.mutator = Mutator(self.aws.sessions[SOURCE], self.root.authorize)
        self.root.authorize()
        return self.mutator

    def delete_version(self, row):
        require(row in self.a['rows'], 'MUTATION_ALLOWLIST_SCOPE')
        return self._mutator(row).delete_version(row)

    def delete_bucket(self):
        return self._mutator('bucket').delete_bucket()
