"""Offline default, explicit read-only metadata/IAM modes, root-gated execution."""
import argparse
import json
import subprocess
import sys
from pathlib import Path
from uuid import uuid4
sys.path.insert(0, str(Path(__file__).resolve().parent))
from safety import *
from root import RootLoader, pins, BOUND_ALLOWLIST

HERE = Path(__file__).resolve().parent


def protected_state(directory):
    validate_local_path(directory)
    validate_local_path(directory/'retirement.journal')
    directory.mkdir(parents=True, exist_ok=True, mode=0o700)
    if sys.platform == 'win32':
        user = subprocess.check_output(['whoami'], text=True).strip()
        subprocess.run(['icacls', str(directory), '/reset'], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       creationflags=subprocess.CREATE_NO_WINDOW)
        subprocess.run(['icacls', str(directory), '/inheritance:r', '/grant:r',
                        user + ':(OI)(CI)F', 'SYSTEM:(OI)(CI)F'], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       creationflags=subprocess.CREATE_NO_WINDOW)
        journal = directory/'retirement.journal'
        if journal.exists():
            validate_local_path(journal)
            subprocess.run(['icacls', str(journal), '/reset'], check=True,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           creationflags=subprocess.CREATE_NO_WINDOW)
            subprocess.run(['icacls', str(journal), '/inheritance:r', '/grant:r', user + ':F', 'SYSTEM:F'],
                           check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           creationflags=subprocess.CREATE_NO_WINDOW)


def permission_observation(aws, allowlist):
    from permission import evaluate, require_allowed, simulate_one
    from policy import source_freeze
    started = iso()
    require(aws.identity(SOURCE) == PRINCIPALS[SOURCE], 'SIMULATION_PRINCIPAL_DRIFT')
    args = {'Bucket': BUCKET, 'ExpectedBucketOwner': SOURCE}
    before = json.loads(aws.client('s3', SOURCE).get_bucket_policy(**args)['Policy'])
    proof, requests = evaluate(aws.client('iam', SOURCE), allowlist, before)
    try:
        require_allowed(proof, allowlist)
        allowed = True
    except Stop:
        allowed = False
    first = allowlist['rows'][0]
    resource = f'arn:aws:s3:::{BUCKET}/{first["key"]}'
    projected = [simulate_one(aws.client('iam', SOURCE), action, resource, source_freeze(), version)
                 for action, version in [('s3:PutObject', None), ('s3:GetObjectVersion', first['source_version']),
                                         ('s3:DeleteObjectVersion', first['source_version'])]]
    after = json.loads(aws.client('s3', SOURCE).get_bucket_policy(**args)['Policy'])
    require(before == after and aws.identity(SOURCE) == PRINCIPALS[SOURCE], 'SIMULATION_BOUNDARY_DRIFT')
    return {'type': 'archive-exact-retirement-permission-proof-v1', 'started_at': started,
            'completed_at': iso(), 'proof': proof, 'request_receipts': requests,
            'all_retirement_decisions_allowed': allowed, 'simulations': len(requests) + len(projected),
            'source_policy': after, 'source_currently_frozen': after == source_freeze(),
            'proposal_simulations': projected, 'proposal_was_applied': False,
            'allowlist_stored_sha256': digest((HERE/'evidence/bound-allowlist.json').read_bytes()),
            'cloud_mutations': 0, 'source_eligibility': 'HOLD', 'payload_downloads': 0}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', nargs='?', choices=['check', 'observe', 'permissions', 'execute'], default='check')
    p.add_argument('--output', type=Path)
    p.add_argument('--gate', type=Path)
    p.add_argument('--gate-sha256')
    p.add_argument('--root-commit')
    p.add_argument('--gate-commit', help='Separate later commit containing the exact gate bytes')
    a = p.parse_args()
    allowlist_bytes = (HERE/'evidence/bound-allowlist.json').read_bytes()
    require(digest(allowlist_bytes) == BOUND_ALLOWLIST, 'ORIGINAL_FULL205_ALLOWLIST_CHANGED')
    allowlist = validate_allowlist(json.loads(allowlist_bytes))
    if a.mode == 'check' and a.gate is None:
        print(json.dumps({'mode': 'check-only-offline', 'versions': 205, 'bytes': 18579936167,
                          'allowlist_stored_sha256': digest(allowlist_bytes), 'root_gate': 'DISABLED',
                          'current_cloud_state': 'NOT_OBSERVED', 'permission_simulation': 'NOT_RUN',
                          'source_eligibility': 'HOLD', 'cloud_requests': 0, 'cloud_mutations': 0}))
        return
    root = None
    if a.mode == 'execute' or a.gate is not None:
        gate_file = a.gate or HERE/'disabled-root-gate.json'
        require(json.loads(gate_file.read_bytes()).get('authorized') is True, 'ROOT_GATE_DISABLED')
        root = RootLoader(gate_file, a.gate_sha256, a.root_commit, a.gate_commit)
        require(root.allowlist_bytes == allowlist_bytes, 'COMMITTED_ROOT_ALLOWLIST_CHANGED')
    if a.mode == 'execute':
        g = root.authorize()
        state = Path(g['execution_state_directory'])
        protected_state(state)
        output = a.output or state/('execution-result-' + str(uuid4()) + '.json')
        require(output.parent.resolve() == state.resolve() and not output.exists(), 'EXECUTION_RECEIPT_DIRECTORY')
    else:
        output = a.output
        require(output is not None and output.parent.is_dir() and not output.exists(),
                'NEW_RECEIPT_IN_EXISTING_OWNED_DIRECTORY_REQUIRED')
    from aws import AWS
    aws = AWS()
    code = pins()
    if a.mode in ('observe', 'permissions'):
        with execution_lock(output.parent):
            if a.mode == 'observe':
                from inventory import observe
                result = observe(aws, allowlist)
                result['permission_simulation'] = 'NOT_RUN-use-permissions-mode'
            else:
                result = permission_observation(aws, allowlist)
            require(pins() == code, 'OBSERVATION_CODE_CHANGED')
            result['code_sha256'] = code
            result['allowlist_stored_sha256'] = digest(allowlist_bytes)
            immutable(output, result)
    else:
        from adapter import ProductionAdapter
        from retirement import run
        execute = a.mode == 'execute'
        g = root.authorize()
        journal = Journal(Path(g['execution_state_directory'])/'retirement.journal',
                          root.expected_hash, digest(allowlist_bytes)) if execute else None
        adapter = ProductionAdapter(aws, root, execute)
        try:
            result = run(adapter, allowlist, root.authorize, journal, execute)
            root.authorize()
            result.update(type='archive-source-retirement-execution-result-v1' if execute else
                          'archive-source-retirement-root-check-result-v1', gate_sha256=root.expected_hash,
                          evidence_commit=root.commit, code_sha256=code,
                          gate_commit=root.gate_commit,
                          journal_sha256=digest(journal.file.read_bytes()) if journal and journal.file.exists() else None,
                          payload_downloads=0)
            immutable(output, result)
            root.authorize()
        except Exception as e:
            failure = output.with_name(output.stem + '-failure-' + str(uuid4()) + '.json')
            immutable(failure, {'type': 'archive-source-retirement-failure-v1', 'at': iso(),
                                'gate_sha256': root.expected_hash, 'evidence_commit': root.commit,
                                'safe_reason': str(e) if isinstance(e, Stop) else type(e).__name__,
                                'journal_sha256': digest(journal.file.read_bytes()) if journal and journal.file.exists() else None,
                                'source_eligibility': 'HOLD'})
            raise
    print(json.dumps({'mode': a.mode, 'file': str(output), 'sha256': digest(output.read_bytes()),
                      'source_eligibility': 'HOLD' if a.mode != 'execute' else 'root-authorized-observation',
                      'payload_downloads': 0}))


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        print(json.dumps({'status': 'refused-or-unproven', 'safe_reason': str(e) if isinstance(e, Stop) else type(e).__name__,
                          'source_eligibility': 'HOLD'}))
        raise SystemExit(1)
