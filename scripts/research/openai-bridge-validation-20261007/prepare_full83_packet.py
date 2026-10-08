"""Prepare exact Full83 shared-runtime bytes locally; never launch or compile."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import uuid
from shared_worker import validate_spec

REPO = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness')
CAPTURE = REPO / 'docs/a8-gcp/r1007/captures/capture-full-a22-hc46-83'
MANIFEST_SHA = 'AEB36ED4DA0D9CED89A0B3D070F7B2ED40D70A7D06CA1589115C526EB981BE5C'
HEAD = '7fc1ec119880be28fe21714ff7e6e681e7dfe4b2'
ORIGIN = '8c3d3f741a1435d671df6325e14e66338a1c22dd'


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest().upper()


def main():
    assert digest(CAPTURE / 'manifest.json') == MANIFEST_SHA
    manifest = json.loads((CAPTURE / 'manifest.json').read_bytes())
    for rel, row in manifest['files'].items():
        path = CAPTURE / rel
        assert path.resolve().is_relative_to(CAPTURE.resolve())
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256'], rel
    heads = json.loads((CAPTURE / 'heads-before.json').read_bytes())
    for ref, expected in [('HEAD', HEAD), ('origin/main', ORIGIN)]:
        actual = subprocess.check_output(['git', '-C', str(REPO), 'rev-parse', ref]).decode().strip()
        assert actual == expected, 'Frozen Git context changed: ' + ref
    assert heads['head'] == HEAD and heads['origin_main'] == ORIGIN
    inner = json.loads((CAPTURE / 'inputs/capture-manifest.json').read_bytes())
    assert len(manifest['project_sources']) == len(inner['project_sources']) == 319
    assert inner['project_sources'] == manifest['project_sources']
    assert inner['stages'] == manifest['stages'] and len(inner['stages']) == 7
    assert inner['requested_axioms'] == manifest['requested_axioms']
    assert len(inner['requested_axioms']) == len(set(inner['requested_axioms'])) == 172
    provenance = inner['cache_provenance']
    assert len(provenance['objects']) == 566
    assert digest(Path('C:/a8gcp/6af6dc24.tar.gz')) == provenance['cloud_archive_sha256']
    objects = {}
    for rel, value in provenance['objects'].items():
        assert rel.startswith('.lake/')
        objects[rel.removeprefix('.lake/')] = value
    run = 'cmmsa_a8_output_' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '_' + uuid.uuid4().hex[:8]
    spec = {'thread': 'cmmsa_full83', 'run': run, 'warm_run': provenance['run'],
            'helper_sha256': manifest['files']['inputs/cloud_capture.py']['sha256'],
            'manifest_sha256': manifest['files']['inputs/capture-manifest.json']['sha256'],
            'warm_hashes': objects}
    validate_spec(spec)
    root = Path('C:/Users/dfred/.quantyra/shared-runtime-packets') / run
    root.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(CAPTURE / 'input-archive.tar.gz', root / 'input-archive.tar.gz')
    assert digest(root / 'input-archive.tar.gz') == manifest['files']['input-archive.tar.gz']['sha256']
    (root / 'spec.json').write_bytes((json.dumps(spec, indent=2) + '\n').encode())
    source = Path(__file__).resolve().parent
    for name in ('shared_worker.py', 'isolated_cache.py', 'thread_leases.py',
                 'lifecycle_manager.py', 'shared_idle.py', 'shared-idle.service.conf'):
        shutil.copyfile(source / name, root / name)
    with tarfile.open(root / 'input-archive.tar.gz', 'r:gz') as archive:
        for member in archive.getmembers():
            assert member.isfile() and not member.name.startswith('/')
            assert all(part not in ('', '.', '..') for part in member.name.split('/'))
    report = {'run': run, 'packet_directory': str(root), 'frozen_manifest_sha256': MANIFEST_SHA,
              'heads': heads, 'verified_capture_files': len(manifest['files']),
              'source_modules': 319, 'native_stages_retained': 7, 'axiom_requests_retained': 172,
              'warm_object_identities': 566, 'files': {p.name: digest(p) for p in root.iterdir()},
              'original_exclusive_resource_policy_retained': manifest['resource_plan'],
              'shared_mode_direction': 'Dan authorized multiple research threads using GCP on 2026-10-07',
              'launch_clearance': False, 'local_compilation': False, 'gcloud_invoked': False,
              'pending': ['Shared runtime and controller enrollment deployment',
                          'Fresh approved preservation/authentication/storage/process gates',
                          'Remote packet preparation and exact-byte verification',
                          'Native terminal and verified custody;qualified shared-mode audit and reviews']}
    (root / 'packet-report.json').write_bytes((json.dumps(report, indent=2) + '\n').encode())
    print(json.dumps(report, indent=2))


if __name__ == '__main__': main()
