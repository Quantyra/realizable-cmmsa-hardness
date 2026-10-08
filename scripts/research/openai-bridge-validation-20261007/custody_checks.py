"""Exact evidence custody and terminal checks; no compiler or VM operations."""
import hashlib
import json
from pathlib import Path
import re
import tarfile


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest().upper()


def verify_local_custody(short_path, repository_path, remote_sha256, remote_bytes):
    if not re.fullmatch(r'[A-F0-9]{64}', remote_sha256): raise ValueError('Invalid remote SHA-256')
    if type(remote_bytes) is not int or remote_bytes <= 0: raise ValueError('Invalid remote archive size')
    paths = [Path(short_path), Path(repository_path)]
    if paths[0].resolve() == paths[1].resolve() or paths[0].samefile(paths[1]):
        raise ValueError('Two distinct custody copies required')
    for path in paths:
        if path.stat().st_size != remote_bytes or digest(path) != remote_sha256:
            raise ValueError('Downloaded custody copy differs from the remote archive')
    return {'short_path': str(paths[0]), 'repository_path': str(paths[1]),
            'remote_sha256': remote_sha256, 'short_sha256': remote_sha256,
            'repository_sha256': remote_sha256, 'bytes': remote_bytes,
            'vm_retained_for_other_threads': True}


def verify_worker_terminal(archive_path, spec):
    with tarfile.open(archive_path, 'r:gz') as archive:
        members = archive.getmembers()
        names = [member.name for member in members]
        if len(names) != len(set(names)): raise ValueError('Ambiguous duplicate evidence entries')
        required = ('shared-worker-terminal.json', 'native-exit', 'finish.native-exit', 'terminal.utc')
        data = {}
        for name in required:
            member = archive.getmember(name)
            if not member.isfile() or member.size > 1024 * 1024: raise ValueError('Invalid terminal evidence member')
            data[name] = archive.extractfile(member).read()
    receipt = json.loads(data['shared-worker-terminal.json'])
    if receipt.get('thread') != spec['thread'] or receipt.get('run') != spec['run'] or receipt.get('spec') != spec:
        raise ValueError('Evidence belongs to a different immutable thread/run')
    if receipt.get('host', {}).get('id') != '8337954477286097405': raise ValueError('Unexpected GCP host')
    if receipt.get('failure') is not None or receipt.get('owned_mounts_released') is not True:
        raise ValueError('Worker failure or owned mount cleanup unresolved')
    native = receipt.get('native_exit')
    if type(native) is not int or native not in (0, 1): raise ValueError('Native terminal unproven')
    if type(receipt.get('finish_native_exit')) is not int or receipt.get('finish_native_exit') != 0 or data['finish.native-exit'].strip() != b'0':
        raise ValueError('Frozen finish helper did not complete')
    if data['native-exit'].strip() != str(native).encode() or not data['terminal.utc'].strip():
        raise ValueError('Terminal receipts disagree')
    return {'native_terminal': True, 'native_exit': native,
            'worker_compile_green': native == 0, 'owned_mounts_released': True,
            'acceptance_audit_and_reviews_required': True}
