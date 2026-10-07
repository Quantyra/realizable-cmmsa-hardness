"""External gate/commit provenance, immutable Git evidence and concrete contracts."""
import json
import re
import subprocess
from pathlib import Path
from safety import *
from inventory import compare_inventory, compare_version_metadata
from policy import source_freeze, destination_custody, policy_value
from retirement import hash_reuse_scope

HERE = Path(__file__).resolve().parent
PARENT = HERE.parents[3] / 'IGH/Quantyra-Planning'
SUPPLEMENT = 'ba9a2880792fc6f1e59ca5bdd95ac4d76276638ddeef747fdb1e814a07914a65'
BOUND_ALLOWLIST = '5856b4c5b62173c5e4fb0f7a3e24299d75414fa2365d3b1d14cd05f0768c2ea8'
ROOT_GATE_PATH = 'docs/aws-migration-2026-10-06/archive-source-retirement-root-gate.json'
PROOF_TYPES = {
    'baseline': 'archive-retirement-readonly-observation-v1',
    'permission': 'archive-exact-retirement-permission-proof-v1',
    'hash_scope': 'archive-independent-hash-reuse-v1',
    'source_freeze': 'archive-source-freeze-operating-proof-v1',
    'destination_custody': 'archive-destination-custody-operating-proof-v1',
    'producer_shutdown': 'archive-producer-shutdown-operating-proof-v1',
    'archive_acceptance': 'archive-combined-root-acceptance-v1',
    'consumer': 'archive-installed-consumer-operating-proof-v1',
    'website': 'archive-global-dns-website-operating-proof-v1',
    'ownership': 'archive-whole-bucket-ownership-operating-proof-v1',
    'dependencies': 'archive-dependencies-operating-proof-v1',
    'code_review': 'archive-source-retirement-independent-code-review-v1',
}
KIND_PROOFS = {
    'archive-independent-acceptance': {'baseline', 'hash_scope', 'archive_acceptance'},
    'installed-restore-consumer': {'consumer'}, 'global-dns-live-website': {'website'},
    'whole-source-ownership': {'ownership'}, 'producer-quiescence': {'producer_shutdown', 'source_freeze', 'permission'},
    'destination-retention-custody': {'destination_custody'},
    'active-dependencies': {'dependencies'}, 'retirement-code-review': {'code_review'},
}


def pins():
    return {p.name: digest(p.read_bytes()) for p in sorted(HERE.iterdir())
            if p.suffix in ('.py', '.mjs')}


class GitEvidence:
    def __init__(self, repo, commit):
        require(re.fullmatch('[a-f0-9]{40}', commit or '') is not None, 'EXPLICIT_ROOT_COMMIT_REQUIRED')
        self.repo, self.commit, self.cache = Path(repo), commit, {}
        result = subprocess.run(['git', 'rev-parse', '--verify', commit + '^{commit}'], cwd=self.repo,
                                capture_output=True, timeout=15)
        require(result.returncode == 0 and result.stdout.decode().strip() == commit, 'ROOT_COMMIT_UNAVAILABLE')

    def read(self, commit, path):
        require(commit == self.commit and path.startswith('docs/aws-migration-2026-10-06/') and
                '\\' not in path and ':' not in path and '..' not in path.split('/'), 'COMMITTED_PROOF_PATH')
        if path not in self.cache:
            result = subprocess.run(['git', 'show', commit + ':' + path], cwd=self.repo,
                                    capture_output=True, timeout=15)
            require(result.returncode == 0 and len(result.stdout) <= 16 * 1024 * 1024,
                    'COMMITTED_PROOF_UNAVAILABLE_OR_TOO_LARGE')
            self.cache[path] = result.stdout  # Immutable object bytes, never worktree flags.
        return self.cache[path]


def concrete_proofs(g, a, read):
    pointers = g['production_proofs']
    require(set(pointers) == set(PROOF_TYPES), 'PRODUCTION_PROOF_COVERAGE')
    proofs = {}
    for name, pin in pointers.items():
        data = read(g['evidence_commit'], pin['path'])
        require(digest(data) == pin['sha256'], 'PRODUCTION_PROOF_PIN')
        p = json.loads(data)
        require(p['type'] == PROOF_TYPES[name], 'CONCRETE_OPERATING_PROOF_REQUIRED')
        proofs[name] = p
    accepted_receipts = set()
    for e in g['evidence']:
        attestation = json.loads(read(g['evidence_commit'], e['path']))
        accepted_receipts.update(p['sha256'] for p in attestation['underlying_proofs'])
        required = KIND_PROOFS[e['kind']]
        require(all(pointers[name] in attestation['underlying_proofs'] for name in required),
                'ACCEPTANCE_NOT_BOUND_TO_PRODUCTION_PROOFS')
    baseline = proofs['baseline']
    require(baseline['identities'] == PRINCIPALS and
            digest(baseline['version_metadata']) == g['version_metadata_sha256'], 'BASELINE_BINDING')
    for account, bucket, field in [(SOURCE, BUCKET, 'source_version'), (DEST, TARGET, 'destination_version')]:
        c = baseline['configuration'][account]
        require(c['bucket'] == bucket and c['expected_owner'] == account, 'BASELINE_OWNER_SCOPE')
        compare_inventory(baseline['inventories'][account], a['rows'], field, c['get_bucket_acl']['Owner']['ID'])
        require(digest(c) == g[('source' if account == SOURCE else 'destination') + '_configuration_sha256'],
                'BASELINE_CONFIGURATION_PIN')
    compare_version_metadata(a, baseline['version_metadata'], baseline['configuration'])
    scope = hash_reuse_scope(a, proofs['hash_scope'])
    from permission import require_allowed
    require_allowed(proofs['permission']['proof'], a)
    require(digest(proofs['permission']['proof']) == g['permission_proof_sha256'], 'ACCEPTED_PERMISSION_PIN')
    require(digest(scope) == g['hash_reuse_scope_sha256'] and
            scope['version_metadata_sha256'] == g['version_metadata_sha256'] and
            re.fullmatch('[a-f0-9]{64}', scope['authentication_proof_sha256']), 'HASH_REUSE_BASELINE_BINDING')
    require(scope['authentication_proof_sha256'] in accepted_receipts, 'AUTHENTICATION_RECEIPT_NOT_COMMITTED')
    require(policy_value(baseline['configuration'][SOURCE]) == source_freeze() and
            policy_value(baseline['configuration'][DEST]) == destination_custody(), 'OPERATING_POLICIES_REQUIRED')
    for name, bucket, policy in [('source_freeze', BUCKET, source_freeze()),
                                 ('destination_custody', TARGET, destination_custody())]:
        p = proofs[name]
        require(p['bucket'] == bucket and p['policy'] == policy and p['policy_sha256'] == digest(policy)
                and p['readback_request_id'] and p['control_custodians'] and p['maintenance_until'] == g['expires_at'],
                'ACTUAL_POLICY_CUSTODY_PROOF_REQUIRED')
    custody = proofs['destination_custody']
    require(custody['versions'] == a['rows'] and custody['catalogs'] == a['catalogs'] and
            custody['key_custody_receipts'] and all(x['custodian'] and x['key_reference'] and
                x['receipt_sha256'] in accepted_receipts and x['source_required'] is False
                for x in custody['key_custody_receipts']), 'DESTINATION_KEY_VERSION_CUSTODY')
    for name in ('producer_shutdown', 'dependencies', 'ownership', 'consumer', 'website',
                 'source_freeze', 'destination_custody'):
        p = proofs[name]
        require(p['packet_sha256'] == PACKET and p['allowlist_sha256'] == g['allowlist_sha256'] and
                p['reviewer_role'] == 'root-independent-verifier' and
                timestamp(g['issued_at']) - 300 <= timestamp(p['observed_at']) <= timestamp(g['issued_at']) and
                timestamp(p['valid_until']) >= timestamp(g['expires_at']), 'OPERATING_PROOF_TTL')
    prod = proofs['producer_shutdown']
    require(prod['bucket'] == BUCKET and prod['topology_receipts'] and
            all(x['sha256'] in accepted_receipts for x in prod['topology_receipts']) and prod['producers'] and
            not prod['unresolved_producers'] and
            all(x['id'] and x['kind'] and x['shutdown_receipt_sha256'] in accepted_receipts and
                x['probe']['kind'] in ('local-pid-absent', 'root-observed-remote-stop') for x in prod['producers']),
            'ACTUAL_PRODUCER_SHUTDOWN_REQUIRED')
    for x in prod['producers']:
        probe = x['probe']
        if probe['kind'] == 'local-pid-absent':
            require(isinstance(probe['pid'], int) and probe['pid'] > 0 and probe['host'], 'PRODUCER_PID_SCOPE')
        else:
            require(probe['operator'] and probe['service_or_host'] and probe['stop_command'] and
                    probe['observed_state'] == 'stopped' and probe['receipt_sha256'] in accepted_receipts,
                    'REMOTE_STOP_RECEIPT_REQUIRED')
    accepted = proofs['archive_acceptance']
    require(accepted['decision'] == 'ACCEPT' and accepted['reviewer_role'] == 'root-independent-verifier' and
            accepted['packet_sha256'] == PACKET and accepted['https_supplement_sha256'] == SUPPLEMENT and
            accepted['catalogs'] == a['catalogs'] and accepted['versions'] == 205 and
            accepted['encrypted_chunks'] == 105 and accepted['authentication_proof_sha256'] == scope['authentication_proof_sha256'],
            'COMBINED_ARCHIVE_ACCEPTANCE_REQUIRED')
    consumer = proofs['consumer']
    require(consumer['account'] == DEST and consumer['principal'] == PRINCIPALS[DEST] and
            consumer['bucket'] == TARGET and consumer['catalogs'] == a['catalogs'] and
            consumer['actual_command'] and re.fullmatch('[a-f0-9]{64}', consumer['installed_config_sha256']) and
            consumer['exit_code'] == 0 and consumer['restored_bytes'] > 0 and
            re.fullmatch('[a-f0-9]{64}', consumer['restored_sha256']) and consumer['exact_versions'] and
            all((v['key'], v['version']) in {(r['key'], r['destination_version']) for r in a['rows']}
                for v in consumer['exact_versions']) and consumer['source_required'] is False,
            'INSTALLED_ACTUAL_CONSUMER_REQUIRED')
    website = proofs['website']
    require(website['account'] == DEST and website['authoritative_nameservers'] and website['delegation_observed'] == website['authoritative_nameservers']
            and website['complete_dns_inventory_sha256'] in accepted_receipts and
            website['tls_fingerprints'] and all(re.fullmatch('[a-f0-9]{64}', f) for f in website['tls_fingerprints'])
            and website['routes'] and website['deployment_command'] and
            all(x['url'].startswith('https://') and x['status'] == 200 and
                re.fullmatch('[a-f0-9]{64}', x['response_sha256']) for x in website['routes']) and
            website['source_required'] is False, 'GLOBAL_DNS_LIVE_WEBSITE_REQUIRED')
    ownership = proofs['ownership']
    require(ownership['bucket'] == BUCKET and ownership['versions'] == a['rows'] and
            ownership['attribution_receipts'] and all(x['sha256'] in accepted_receipts for x in ownership['attribution_receipts'])
            and ownership['unresolved_bucket_data'] == [] and
            ownership['retained_shared_principals'] == list(PRINCIPALS.values())[:1] and
            ownership['other_buckets_in_scope'] == [], 'WHOLE_BUCKET_EXCLUSIVE_OWNERSHIP_REQUIRED')
    deps = proofs['dependencies']
    require(deps['bucket'] == BUCKET and deps['examined_surfaces'] and deps['findings'] and
            not deps['unresolved_for_bucket'] and
            all(x['surface'] and x['disposition'] in ('destination-consumer', 'stopped-producer', 'historical-only') and
                x['receipt_sha256'] in accepted_receipts for x in deps['findings']),
            'SUBSTANTIVE_DEPENDENCY_DISPOSITION_REQUIRED')
    review = proofs['code_review']
    require(review['decision'] in ('GO', 'GO-WITH-BOUNDARIES') and
            review['reviewer_role'] == 'independent-retirement-code-reviewer' and review['code_sha256'] == g['code_sha256'] and
            review['botocore'] == '1.43.108' and review['boto3'] == '1.43.108' and
            review['transport_receipt_sha256'] in accepted_receipts and review['findings'], 'INDEPENDENT_INTEGRATION_REVIEW_REQUIRED')
    return proofs


class RootLoader:
    def __init__(self, file, expected_hash, commit, gate_commit, repo=PARENT):
        self.file, self.expected_hash, self.commit = Path(file), expected_hash, commit
        self.gate_commit = gate_commit
        require(re.fullmatch('[a-f0-9]{64}', expected_hash or '') is not None, 'EXTERNAL_GATE_HASH_REQUIRED')
        raw = self.file.read_bytes()
        require(digest(raw) == expected_hash, 'EXTERNAL_GATE_HASH')
        gate = json.loads(raw)
        require(gate.get('authorized') is True and gate.get('execution_cli_enabled') is True,
                'ROOT_GATE_DISABLED')
        require(gate['evidence_commit'] == commit, 'EXTERNAL_ROOT_COMMIT_MISMATCH')
        self.git = GitEvidence(repo, commit)
        self.gate_git = GitEvidence(repo, gate_commit)
        self.allowlist_bytes = self.git.read(commit, gate['root_allowlist_path'])
        require(digest(self.allowlist_bytes) == BOUND_ALLOWLIST, 'ORIGINAL_FULL205_ALLOWLIST_CHANGED')
        self.allowlist = validate_allowlist(json.loads(self.allowlist_bytes))
        self.proofs = None
        self.authorize()

    def authorize(self):
        raw = self.file.read_bytes()
        require(self.gate_git.read(self.gate_commit, ROOT_GATE_PATH) == raw, 'COMMITTED_ROOT_GATE_REQUIRED')
        g = load_gate(raw, self.expected_hash, self.allowlist_bytes, self.git.read, pins, now=clock)
        require(g['evidence_commit'] == self.commit and g['execution_cli_enabled'] is True,
                'ROOT_COMMIT_OR_MODE_DRIFT')
        if self.proofs is None:
            # Safe reuse of validated immutable Git blobs only. Gate/code pins and
            # all TTL checks still reload on every authorization; live state never
            # comes from this cache.
            self.proofs = concrete_proofs(g, self.allowlist, self.git.read)
        # All proof and Git reads finish before this final expiry check.
        require(timestamp(g['issued_at']) <= clock() < timestamp(g['expires_at']), 'ROOT_GATE_EXPIRED')
        return g
