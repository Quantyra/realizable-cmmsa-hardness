"""Materialize complete pinned project bodies and external boundary source context."""
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02')
PLANNING = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    qualification = ROOT/'consumption-v2/qualification'
    trace = json.loads((qualification/'type-dag-qualification.json').read_bytes())
    graphs = json.loads((qualification/'graphs/validated-graphs.json').read_bytes())
    minimum = json.loads((PLANNING/'docs/research/pvnp/full89-current-minimum-critical-body-pins-2026-10-07.json').read_bytes())
    capture = ROOT/'input-archive.tar.gz'
    if sha(capture.read_bytes()) != minimum['input_archive_sha256']:
        raise ValueError('Changed Full89 capsule')
    terminal_path = ROOT/'consumption-v2/checks/20261008T112643080244Z/vm-termination.json'
    termination = json.loads(terminal_path.read_bytes())
    if termination['independent']['status'] != 'TERMINATED' or termination['independent']['id'] != '7237681467779354904':
        raise ValueError('Dedicated termination not proven')
    result = qualification/'review-sources'
    result.mkdir()
    project = {f'lean/{module.replace(".", "/")}.lean' for module in trace['project_modules']}
    minimum_paths = {row['path'] for row in minimum['bodies']}
    selected = project | minimum_paths
    rows = []
    with tarfile.open(capture) as archive:
        manifest_data = archive.extractfile('capture-manifest.json').read()
        if sha(manifest_data) != minimum['capture_manifest_sha256']:
            raise ValueError('Changed capture manifest')
        manifest = json.loads(manifest_data)
        for path, pin in manifest['project_sources'].items():
            data = archive.extractfile(path).read()
            if sha(data) != pin['sha256'] or len(data) != pin['bytes']:
                raise ValueError('Source pin mismatch: ' + path)
            if path in selected:
                dest = result/path
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
                rows.append({'path': path, 'sha256': sha(data), 'bytes': len(data),
                             'transitively_consumed': path in project, 'minimum_required': path in minimum_paths,
                             'complete_body': True})
        if len(rows) != len(selected):
            raise ValueError('Selected project body missing')
    native_path = Path('C:/a8gcp/e93b94e1.tar.gz')
    if sha(native_path.read_bytes()) != '0ECFA6657CEB08927A2ED197363DD2539A3319AC8F3945C02BB077AC67424A64':
        raise ValueError('Changed native custody archive')
    with tarfile.open(native_path) as native:
        package_pins = json.load(native.extractfile('package-source-hashes.json'))
        core_pins = json.load(native.extractfile('core-source-hashes.json'))
        revisions = json.load(native.extractfile('package-identities.json'))
        packages = tarfile.open(fileobj=io.BytesIO(native.extractfile('package-sources.tar.gz').read()))
        core = tarfile.open(fileobj=io.BytesIO(native.extractfile('core-sources.tar.gz').read()))
        boundary_sources = {}
        for module in sorted({row['module'] for row in trace['external_boundaries'].values()}):
            root = module.split('.')[0]
            relative = module.replace('.', '/') + '.lean'
            if root == 'Init':
                source_path = 'src/lean/' + relative
                data = core.extractfile(source_path).read()
                pin = core_pins[source_path]
                revision = 'Lean v4.34.0-rc2; exact core-source pin'
            elif root in ('Mathlib', 'Batteries'):
                package = root.lower()
                source_path = '.lake/packages/' + package + '/' + relative
                data = packages.extractfile(source_path).read()
                pin = package_pins[source_path]
                revision = revisions[package]
            else:
                raise ValueError('Unmapped external boundary: ' + module)
            if sha(data) != pin:
                raise ValueError('External source pin mismatch: ' + module)
            dest = result/'external'/relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            boundary_sources[module] = {'source_path': source_path, 'packet_path': 'external/' + relative,
                                         'sha256': pin, 'bytes': len(data), 'revision': revision,
                                         'complete_source': True}
    boundary_rows = []
    for constant, row in trace['external_boundaries'].items():
        boundary_rows.append({'constant': constant, **row, 'source': boundary_sources[row['module']],
                              'disposition': 'pinned kernel/library boundary with complete source available; independent review pending'})
    index = {'schema': 'full89-complete-consumption-review-sources-v1',
             'roots': graphs['graphs']['exact172-native']['roots'], 'project_bodies': rows,
             'project_body_count': len(rows), 'project_body_bytes': sum(r['bytes'] for r in rows),
             'consumed_project_modules': len(project), 'external_boundaries': boundary_rows,
             'external_module_count': len(boundary_sources),
             'external_source_bytes': sum(r['bytes'] for r in boundary_sources.values()),
             'type_dag_qualification_sha256': sha((qualification/'type-dag-qualification.json').read_bytes()),
             'termination': termination,
             'selection_complete_for_native172_and_minimum': True,
             'external_source_custody_complete': True,
             'independent_boundary_review_complete': False,
             'provider_context_fit_verified': False, 'reviewed': False, 'accepted': False,
             'scope': 'Original A22/HC46/selected-consumer milestone only; remaining full-manuscript obligations are not closed.'}
    (result/'source-index.json').write_text(json.dumps(index, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: index[k] for k in ('project_body_count', 'project_body_bytes', 'external_module_count', 'external_source_bytes')}))


if __name__ == '__main__':
    main()
