"""GCP-only frozen-packet preparation and inspection. Never invokes Lean/Lake."""
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import sys
import tarfile
from shared_worker import validate_spec


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest().upper()


def prepare(stage):
    if sys.platform != 'linux': raise RuntimeError('Remote packet preparation requires Linux')
    stage = Path(stage).resolve(strict=True)
    report = json.loads((stage / 'packet-report.json').read_bytes())
    for name, expected in report['files'].items():
        if '/' in name or '\\' in name: raise ValueError('Invalid packet leaf')
        if digest(stage / name) != expected: raise RuntimeError('Packet byte identity mismatch: ' + name)
    spec = json.loads((stage / 'spec.json').read_bytes()); validate_spec(spec)
    home = Path.home().resolve()
    if str(home) != '/home/dfredriksen_quantyra_org': raise RuntimeError('Unexpected VM user')
    work = home / spec['run']
    owner = {'thread': spec['thread'], 'run': spec['run']}
    if work.exists():
        if work.is_symlink() or json.loads((work / '.shared-run-owner.json').read_bytes()) != owner:
            raise RuntimeError('Existing workspace is not owned by this packet')
        created = False
    else:
        work.mkdir(); created = True
        (work / '.shared-run-owner.json').write_text(json.dumps(owner) + '\n')
    with tarfile.open(stage / 'input-archive.tar.gz', 'r:gz') as archive:
        members = archive.getmembers()
        names = [member.name for member in members]
        if len(names) != len(set(names)): raise ValueError('Duplicate capsule entries')
        for member in members:
            parts = member.name.split('/')
            if not member.isfile() or member.name.startswith('/') or any(p in ('', '.', '..') for p in parts):
                raise ValueError('Unsafe capsule member')
            if parts[0] in ('.lake', '.shared-run-owner.json', 'cache-mount', 'offline-bin'):
                raise ValueError('Capsule overwrites runtime controls')
            data = archive.extractfile(member).read()
            target = work / member.name
            if created:
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open('xb') as stream: stream.write(data)
            elif target.read_bytes() != data:
                raise RuntimeError('Prepared workspace drift: ' + member.name)
    if digest(work / 'cloud_capture.py') != spec['helper_sha256'] or digest(work / 'capture-manifest.json') != spec['manifest_sha256']:
        raise RuntimeError('Extracted helper/manifest mismatch')
    frozen = runpy.run_path(str(work / 'cloud_capture.py'), run_name='remote_packet_preflight')
    manifest = json.loads((work / 'capture-manifest.json').read_bytes())
    identity = frozen['require_gcp'](manifest)
    frozen['source_pins'](work, manifest)
    warm = home / spec['warm_run'] / '.lake'
    for rel, expected in spec['warm_hashes'].items():
        if not (warm / rel).resolve(strict=True).is_relative_to(warm.resolve(strict=True)):
            raise RuntimeError('Warm cache escapes its root')
        if digest(warm / rel) != expected: raise RuntimeError('Warm object drift: ' + rel)
    result = {'run': spec['run'], 'workspace': str(work), 'created_workspace': created,
              'gcp_identity': identity, 'input_archive_sha256': digest(stage / 'input-archive.tar.gz'),
              'capsule_files_verified': len(members), 'project_sources_verified': len(manifest['project_sources']),
              'warm_objects_verified': len(spec['warm_hashes']), 'disk_available_bytes': shutil.disk_usage(home).free,
              'lean_invoked': False, 'vm_power_operations': False, 'launch_clearance': False}
    (stage / 'remote-preparation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__': prepare(sys.argv[1])
