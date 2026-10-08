"""GCP thread executor for an already extracted, byte-verified frozen capture.

Never starts/stops a VM, installs a global timer, or releases a custody lease.
The local controller must verify frozen HEAD/preservation/storage gates, upload
the immutable capsule, and retain one handle through terminal and custody.
"""
import hashlib
import json
import os
from pathlib import Path
import runpy
import re
import subprocess
import sys
import tarfile
import traceback
from datetime import datetime, timezone
from isolated_cache import CacheMount
from thread_leases import acquire, checked


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest().upper()


def validate_spec(spec):
    checked(spec['thread'])
    for key in ('run', 'warm_run'):
        if not re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}', spec[key]):
            raise ValueError('Invalid immutable run identity')
    if spec['run'] == spec['warm_run']: raise ValueError('Run cannot reuse its own writable cache')
    hashes = spec['warm_hashes']
    if not isinstance(hashes, dict) or not hashes: raise ValueError('Missing warm-cache provenance')
    for rel, value in hashes.items():
        if rel.startswith('/') or '\\' in rel or any(part in ('', '.', '..') for part in rel.split('/')):
            raise ValueError('Invalid warm-cache relative path')
    for value in [spec['helper_sha256'], spec['manifest_sha256'], *hashes.values()]:
        if not isinstance(value, str) or not re.fullmatch(r'[A-F0-9]{64}', value):
            raise ValueError('Invalid exact-byte SHA-256 identity')


def owned_processes(workspace):
    result = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid(): continue
        try:
            cwd = (path / 'cwd').resolve(strict=True)
            if cwd == workspace or workspace in cwd.parents: result.append(int(path.name))
        except FileNotFoundError: continue
        except PermissionError:
            try:
                status = (path / 'status').read_text()
                uid = int(next(line for line in status.splitlines() if line.startswith('Uid:')).split()[2])
                if uid == os.geteuid(): result.append(int(path.name))
            except FileNotFoundError: continue
            except Exception: result.append(int(path.name))
    return result


def execute(spec):
    if sys.platform != 'linux': raise RuntimeError('GCP-only worker')
    validate_spec(spec)
    home = Path.home().resolve()
    if str(home) != '/home/dfredriksen_quantyra_org': raise RuntimeError('Unexpected execution user')
    run, thread = checked(spec['run']), checked(spec['thread'])
    work = home / run
    warm = home / checked(spec['warm_run']) / '.lake'
    evidence = home / 'cmmsa-evidence' / (run + '-evidence')
    registry = Path('/var/lib/quantyra-thread-leases')
    readiness = json.loads((registry / 'runtime-readiness.json').read_bytes())
    if readiness.get('ready') is not True or readiness.get('vm_id') != '8337954477286097405':
        raise RuntimeError('Shared runtime deployment/admission not verified')
    if not work.is_dir() or work.is_symlink(): raise RuntimeError('Missing owned extracted workspace')
    if json.loads((work / '.shared-run-owner.json').read_bytes()) != {'thread': thread, 'run': run}:
        raise RuntimeError('Workspace ownership mismatch')
    helper = work / 'cloud_capture.py'
    manifest_path = work / 'capture-manifest.json'
    if digest(helper) != spec['helper_sha256'] or digest(manifest_path) != spec['manifest_sha256']:
        raise RuntimeError('Frozen cloud helper/manifest identity mismatch')
    manifest = json.loads(manifest_path.read_bytes())
    frozen = runpy.run_path(str(helper), run_name='frozen_shared_cloud_helper')
    # Original immutable helper checks authenticated GCP metadata before every
    # compiler command, and retains the original stages/source/dependency gates.
    identity = frozen['require_gcp'](manifest)
    frozen['source_pins'](work, manifest)
    for rel, expected in spec['warm_hashes'].items():
        path = warm / rel
        if not path.resolve(strict=True).is_relative_to(warm.resolve(strict=True)):
            raise RuntimeError('Warm-cache identity escapes its root')
        if digest(path) != expected: raise RuntimeError('Warm-cache identity mismatch: ' + rel)
    if not spec['warm_hashes']: raise RuntimeError('Missing warm-cache provenance')
    if evidence.exists(): raise RuntimeError('Evidence destination already exists')
    lease = acquire(registry, thread, run)
    evidence.mkdir(parents=True)
    (evidence / 'started.utc').write_text(datetime.now(timezone.utc).isoformat() + '\n')
    (evidence / 'run-id.txt').write_text(run + '\n')
    cache = CacheMount(work, warm)
    failure = None; native = None; finish_native = None
    try:
        cache.open()
        offline = work / 'offline-bin'; offline.mkdir()
        git = offline / 'git'
        git.write_text('#!/usr/bin/env bash\ncase "$1" in clone|fetch|pull|ls-remote) exit 93;; esac\nexec /usr/bin/git "$@"\n')
        git.chmod(0o755)
        environment = dict(os.environ)
        environment['PATH'] = str(offline) + ':' + str(home / '.elan/bin') + ':' + environment['PATH']
        for action in ('begin', 'compile'):
            label = 'setup' if action == 'begin' else action
            with (evidence / (label + '.stdout')).open('xb') as out, (evidence / (label + '.stderr')).open('xb') as err:
                child = subprocess.Popen([sys.executable, str(helper), action, str(evidence)],
                                         cwd=work, env=environment, stdout=out, stderr=err)
                (lease / 'active-process.json').write_text(json.dumps({'pid': child.pid, 'action': action}) + '\n')
                code = child.wait()  # No timeout-triggered restart or duplicate.
                (evidence / (action + '.native-exit')).write_text(str(code) + '\n')
                native = code
                if code: break
        with (evidence / 'finish.stdout').open('xb') as out, (evidence / 'finish.stderr').open('xb') as err:
            finish_native = subprocess.run([sys.executable, str(helper), 'finish', str(evidence)],
                                          cwd=work, env=environment, stdout=out, stderr=err).returncode
        (evidence / 'finish.native-exit').write_text(str(finish_native) + '\n')
        if finish_native: raise RuntimeError('Frozen finish helper failed')
        survivors = owned_processes(work)
        if survivors: raise RuntimeError('Owned processes still active: ' + repr(survivors))
    except Exception:
        failure = traceback.format_exc()
    finally:
        try: cache.close()
        except Exception: failure = (failure or '') + '\nMount cleanup:\n' + traceback.format_exc()
        try:
            for rel, expected in spec['warm_hashes'].items():
                if digest(warm / rel) != expected: raise RuntimeError('Shared lower cache drift: ' + rel)
        except Exception: failure = (failure or '') + '\nWarm-cache custody:\n' + traceback.format_exc()
        receipt = {'thread': thread, 'run': run, 'host': identity, 'native_exit': native,
                   'finish_native_exit': finish_native, 'failure': failure,
                   'owned_mounts_released': not cache.mounted, 'mount_commands': cache.receipts,
                   'lease_retained_for_verified_custody': True, 'vm_power_operations': False,
                   'local_compilation': False, 'spec': spec}
        (evidence / 'shared-worker-terminal.json').write_text(json.dumps(receipt, indent=2) + '\n')
        (evidence / 'terminal.utc').write_text(datetime.now(timezone.utc).isoformat() + '\n')
        (evidence / 'native-exit').write_text(str(0 if native == finish_native == 0 and failure is None else 1) + '\n')
        archive = evidence.with_name(evidence.name + '.tar.gz')
        next_archive = archive.with_name(archive.name + '.next')
        with tarfile.open(next_archive, 'w:gz') as output:
            for path in sorted(evidence.iterdir()): output.add(path, arcname=path.name)
        next_archive.replace(archive)
        print(json.dumps({'archive': str(archive), 'sha256': digest(archive), 'lease_retained': True}))
    return 0 if native == finish_native == 0 and failure is None else 1


if __name__ == '__main__':
    raise SystemExit(execute(json.loads(Path(sys.argv[1]).read_bytes())))
