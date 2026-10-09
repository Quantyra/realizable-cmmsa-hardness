"""Materialize complete pinned project bodies and external boundary source context."""
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full100-matrix-fourier-bullet-repair-resource02')
PLANNING = Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning')


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def write_pinned(path, data):
    if path.exists():
        if path.read_bytes() != data: raise ValueError('Partial source recovery identity mismatch: '+str(path))
    else:
        with path.open('xb') as output: output.write(data)


def main():
    qualification = ROOT/'consumption-v2/qualification'
    trace = json.loads((qualification/'type-dag-qualification.json').read_bytes())
    graphs = json.loads((qualification/'graphs/validated-graphs.json').read_bytes())
    summary = json.loads((qualification/'qualification-summary.json').read_bytes())
    manifest_now = json.loads((ROOT/'capture-manifest.json').read_bytes())
    marker_now = json.loads((ROOT/'launch-once.json').read_bytes())
    if not summary['structural_trace_qualification'] or summary['run'] != marker_now['run'] or any(summary['unresolved_by_graph'].values()):
        raise ValueError('Own qualified complete trace required')
    if graphs['graphs']['exact192-native']['roots'] != manifest_now['requested_axioms'] or len(graphs['graphs']['focused-twentyfour-consumer']['roots']) != 24:
        raise ValueError('Complete192/focused24 native trace scope required')
    minimum = json.loads((PLANNING/'docs/research/pvnp/full89-current-minimum-critical-body-pins-2026-10-07.json').read_bytes())
    capture = ROOT/'input-archive.tar.gz'
    binding=json.loads((ROOT/'resource-binding.json').read_bytes())
    if sha(capture.read_bytes()) != binding['files']['input-archive.tar.gz']:
        raise ValueError('Changed Full100 capsule')
    trace_marker=json.loads((ROOT/'consumption-v2/launch-once.json').read_bytes())
    terminal_path = Path(trace_marker['preflight'])/'vm-termination.json'
    termination = json.loads(terminal_path.read_bytes())
    if termination['independent']['status'] != 'TERMINATED' or termination['independent']['id'] != '7237681467779354904':
        raise ValueError('Dedicated termination not proven')
    result = qualification/'review-sources'
    result.mkdir(exist_ok=True)
    if (result/'source-index.json').exists(): raise ValueError('Completed source index already exists; inspect it')
    project = {f'lean/{module.replace(".", "/")}.lean' for module in trace['project_modules']}
    minimum_paths = {row['path'] for row in minimum['bodies']}
    selected = set(json.loads((ROOT/'capture-manifest.json').read_bytes())['project_sources'])
    if len(selected) != 327 or not (project | minimum_paths) <= selected: raise ValueError('Complete captured project scope missing')
    rows = []
    with tarfile.open(capture) as archive:
        manifest_data = archive.extractfile('capture-manifest.json').read()
        if sha(manifest_data) != binding['files']['capture-manifest.json']:
            raise ValueError('Changed capture manifest')
        manifest = json.loads(manifest_data)
        for path, pin in manifest['project_sources'].items():
            data = archive.extractfile(path).read()
            if sha(data) != pin['sha256'] or len(data) != pin['bytes']:
                raise ValueError('Source pin mismatch: ' + path)
            if path in selected:
                dest = result/path
                dest.parent.mkdir(parents=True, exist_ok=True)
                write_pinned(dest, data)
                rows.append({'path': path, 'sha256': sha(data), 'bytes': len(data),
                             'transitively_consumed': path in project, 'minimum_required': path in minimum_paths,
                             'complete_body': True})
        if len(rows) != len(selected):
            raise ValueError('Selected project body missing')
    native_marker=json.loads((ROOT/'launch-once.json').read_bytes())
    native_custody=json.loads((Path(native_marker['preflight'])/'terminal-custody.json').read_bytes())['custody']
    native_path = Path(native_custody['repository_path'])
    if sha(native_path.read_bytes()) != native_custody['remote_sha256']:
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
            elif root in ('Mathlib', 'Batteries', 'Complexitylib'):
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
            write_pinned(dest, data)
            boundary_sources[module] = {'source_path': source_path, 'packet_path': 'external/' + relative,
                                         'sha256': pin, 'bytes': len(data), 'revision': revision,
                                         'complete_source': True,
                                         'additional_independent_review_required': root == 'Complexitylib'}
    boundary_rows = []
    for constant, row in trace['external_boundaries'].items():
        boundary_rows.append({'constant': constant, **row, 'source': boundary_sources[row['module']],
                              'disposition': 'pinned kernel/library boundary with complete source available; independent review pending'})
    index = {'schema': 'full100-complete-captured-project-and-consumption-review-sources-v1',
             'roots': graphs['graphs']['exact192-native']['roots'], 'project_bodies': rows,
             'project_body_count': len(rows), 'project_body_bytes': sum(r['bytes'] for r in rows),
             'consumed_project_modules': len(project), 'external_boundaries': boundary_rows,
             'external_module_count': len(boundary_sources),
             'external_source_bytes': sum(r['bytes'] for r in boundary_sources.values()),
             'type_dag_qualification_sha256': sha((qualification/'type-dag-qualification.json').read_bytes()),
             'termination': termination,
             'selection_complete_for_native192_and_entire_capture': True,
             'external_source_custody_complete': True,
             'additional_boundary_review_modules': [module for module, row in boundary_sources.items()
                                                     if row['additional_independent_review_required']],
             'independent_boundary_review_complete': False,
             'provider_context_fit_verified': False, 'reviewed': False, 'accepted': False,
             'scope': 'All327 complete captured project bodies, exact192 roots/focused-twentyfour including same material consumer. Unreached declarations have compile evidence only; full material and manuscript obligations remain open.'}
    (result/'source-index.json').write_text(json.dumps(index, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: index[k] for k in ('project_body_count', 'project_body_bytes', 'external_module_count', 'external_source_bytes')}))


if __name__ == '__main__':
    main()
