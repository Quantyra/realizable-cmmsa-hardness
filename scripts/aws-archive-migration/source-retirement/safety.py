"""Archive-only preparation contracts. No credential or payload handling."""
import hashlib
import json
import os
import re
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path

SOURCE = '485386182336'
DEST = '063280428495'
BUCKET = f'quantyra-research-archive-{SOURCE}-us-east-1'
TARGET = f'quantyra-research-archive-{DEST}-us-east-1'
PACKET = '713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce'
PRINCIPALS = {SOURCE: f'arn:aws:iam::{SOURCE}:user/cyint-ea',
              DEST: f'arn:aws:iam::{DEST}:user/ServiceAdmin'}
KINDS = {'archive-independent-acceptance', 'installed-restore-consumer',
         'global-dns-live-website', 'whole-source-ownership', 'producer-quiescence',
         'destination-retention-custody', 'active-dependencies', 'retirement-code-review'}


class Stop(Exception):
    pass


def require(ok, code):
    if not ok:
        raise Stop(code)


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False,
                      default=lambda x: x.isoformat()).encode()


def digest(value):
    return hashlib.sha256(value if isinstance(value, bytes) else encoded(value)).hexdigest()


def clock():
    return datetime.now(timezone.utc).timestamp()


def iso():
    return datetime.now(timezone.utc).isoformat()


def timestamp(s):
    d = datetime.fromisoformat(s.replace('Z', '+00:00'))
    require(d.tzinfo is not None, 'TIMEZONE_REQUIRED')
    return d.timestamp()


def immutable(file, value):
    with Path(file).open('xb') as f:
        f.write(encoded(value) + b'\n')
        f.flush()
        os.fsync(f.fileno())


@contextmanager
def execution_lock(directory):
    file = Path(directory) / 'execution.lock'
    immutable(file, {'pid': os.getpid(), 'at': iso()})
    try:
        yield
    finally:
        file.unlink()  # No stale-lock removal on acquisition failure.


def validate_allowlist(a):
    require(a['type'] == 'archive-retirement-allowlist-v1' and a['packet_sha256'] == PACKET,
            'ALLOWLIST_PACKET')
    require(a['source'] == BUCKET and a['destination'] == TARGET, 'BUCKET_SCOPE')
    rows = a['rows']
    require(len(rows) == 205 and sum(r['bytes'] for r in rows) == 18579936167, 'FULL205_SCOPE')
    for field in ('source_version', 'destination_version'):
        identities = [(r['key'], r[field]) for r in rows]
        require(len(set(identities)) == 205, 'NONINJECTIVE_MAPPING')
        require(all(isinstance(v, str) and v not in ('', 'null') for _, v in identities),
                'IMMUTABLE_VERSION_REQUIRED')
    require(all(isinstance(r['key'], str) and r['key'] and '*' not in r['key'] and
                re.fullmatch('[a-f0-9]{64}', r['sha256']) and
                isinstance(r['bytes'], int) and r['bytes'] >= 0 for r in rows), 'BAD_ROW')
    require(len(a['catalogs']) == 45 and len(a['packet_artifacts']) == 305, 'FULL_PIN_SCOPE')
    return a


def load_gate(raw, expected_hash, allowlist_bytes, read_committed, local_pins, now=clock):
    """read_committed(commit,path) must read Git blobs, never worktree attestations."""
    require(digest(raw) == expected_hash, 'EXTERNAL_GATE_HASH')
    g = json.loads(raw)
    require(g.get('type') == 'archive-retirement-root-gate-v1' and
            g.get('authorized') is True and g.get('decision') == 'ACCEPT', 'ROOT_GATE_DISABLED')
    require(g['packet_sha256'] == PACKET and g['allowlist_sha256'] == digest(allowlist_bytes),
            'ROOT_ALLOWLIST_BINDING')
    validate_allowlist(json.loads(allowlist_bytes))
    require(re.fullmatch('[a-f0-9]{40}', g['evidence_commit']) is not None, 'EVIDENCE_COMMIT')
    require(g['root_allowlist_path'] == 'docs/aws-migration-2026-10-06/archive-source-retirement-allowlist.json'
            and read_committed(g['evidence_commit'], g['root_allowlist_path']) == allowlist_bytes,
            'DISTINCT_COMMITTED_ROOT_ALLOWLIST_REQUIRED')
    require(g['principals'] == PRINCIPALS and g['source'] == BUCKET and
            g['destination'] == TARGET, 'ROOT_PRINCIPAL_SCOPE')
    require(Path(g['execution_state_directory']).resolve() ==
            (Path.home()/'.quantyra/aws-migration-20261006/source-retirement-execution').resolve(),
            'FIXED_SHARED_EXECUTION_DIRECTORY_REQUIRED')
    start, end = timestamp(g['issued_at']), timestamp(g['expires_at'])
    require(0 < end - start <= 3600 and start <= now() < end, 'ROOT_GATE_EXPIRED')
    require(g['code_sha256'] == local_pins(), 'REVIEWED_CODE_CHANGED')
    evidence = g['evidence']
    require(len(evidence) == len(KINDS) and {x['kind'] for x in evidence} == KINDS,
            'EVIDENCE_COVERAGE')
    for pin in evidence:
        require(pin['path'].startswith('docs/aws-migration-2026-10-06/') and
                '..' not in pin['path'].split('/'), 'EVIDENCE_PATH')
        data = read_committed(g['evidence_commit'], pin['path'])
        require(digest(data) == pin['sha256'], 'EVIDENCE_PIN')
        e = json.loads(data)
        require(e['type'] == 'archive-retirement-attestation-v1' and
                e['kind'] == pin['kind'] and e['decision'] == 'ACCEPT' and
                e['packet_sha256'] == PACKET and e['allowlist_sha256'] == g['allowlist_sha256'] and
                e['underlying_proofs'] and e['reviewer_role'] == 'root-independent-verifier',
                'SUBSTANTIVE_ROOT_ATTESTATION_REQUIRED')
        require(timestamp(e['observed_at']) <= now() < timestamp(e['valid_until']) and
                timestamp(e['valid_until']) >= end, 'EVIDENCE_FRESHNESS')
        for proof in e['underlying_proofs']:
            require(proof['path'].startswith('docs/aws-migration-2026-10-06/') and
                    '..' not in proof['path'].split('/'), 'PROOF_PATH')
            require(digest(read_committed(g['evidence_commit'], proof['path'])) == proof['sha256'],
                    'UNDERLYING_PROOF_PIN')
    require(all(isinstance(g[k], str) and re.fullmatch('[a-f0-9]{64}', g[k]) for k in
                ('source_configuration_sha256', 'destination_configuration_sha256',
                 'version_metadata_sha256', 'permission_proof_sha256', 'hash_reuse_scope_sha256')),
            'CURRENT_CONFIGURATION_PROOFS_REQUIRED')
    require(g['preserve_keys_catalogs_local_source'] is True and
            g['shared_principals_roles_retained'] is True, 'PRESERVATION_REQUIRED')
    require(start <= now() < end, 'ROOT_GATE_EXPIRED')
    return {**g, '_gate_sha256': expected_hash, '_allowlist_sha256': digest(allowlist_bytes)}


class Journal:
    """Exclusive writer required. Torn bytes are preserved and block all progress."""
    def __init__(self, file, gate_hash, allowlist_hash):
        self.file = Path(file)
        self.binding = {'gate_sha256': gate_hash, 'allowlist_sha256': allowlist_hash}
        self.events = []
        if self.file.exists():
            raw = self.file.read_bytes()
            require(not raw or raw.endswith(b'\n'), 'TORN_JOURNAL')
            for line in raw.splitlines():
                try:
                    event = json.loads(line)
                except ValueError:
                    raise Stop('TORN_JOURNAL')
                payload = {k: v for k, v in event.items() if k != 'sha256'}
                require(event['sha256'] == digest(payload) and
                        event['previous'] == (self.events[-1]['sha256'] if self.events else None) and
                        event['binding'] == self.binding and event['sequence'] == len(self.events),
                        'JOURNAL_BINDING_OR_CHAIN')
                self._validate(payload)
                self.events.append(event)

    def _validate(self, p):
        require(p['kind'] in ('intent', 'confirmed', 'terminal'), 'JOURNAL_EVENT')
        require(p['operation'] in ('bucket', 'version') and
                ((p['operation'] == 'bucket' and p['identity'] == BUCKET) or
                 (p['operation'] == 'version' and isinstance(p['identity'], list) and
                  len(p['identity']) == 2 and all(isinstance(x, str) and x for x in p['identity']))),
                'JOURNAL_OPERATION_SCOPE')
        if p['kind'] == 'intent':
            require(not self.find(p['operation'], p['identity'], 'intent'), 'DUPLICATE_INTENT')
        if p['kind'] == 'confirmed':
            require(self.find(p['operation'], p['identity'], 'intent') and
                    not self.find(p['operation'], p['identity'], 'confirmed'), 'CONFIRMATION_WITHOUT_INTENT')

    def find(self, operation, identity, kind):
        return [e for e in self.events if e['operation'] == operation and
                e['identity'] == identity and e['kind'] == kind]

    def append(self, kind, operation, identity, **details):
        p = {'sequence': len(self.events), 'previous': self.events[-1]['sha256'] if self.events else None,
             'binding': self.binding, 'kind': kind, 'operation': operation,
             'identity': identity, 'at': iso(), 'details': details}
        self._validate(p)
        event = {**p, 'sha256': digest(p)}
        # append+fsync before request, and after confirmation; never rewrite a chain.
        with self.file.open('ab') as f:
            f.write(encoded(event) + b'\n')
            f.flush()
            os.fsync(f.fileno())
        self.events.append(event)
        return event
