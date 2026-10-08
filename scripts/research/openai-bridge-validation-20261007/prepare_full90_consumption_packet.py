"""Reuse the proven shared-DAG probe with exact173/focused-five successor scope."""
import ast
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full90 import OUTPUT, REQUEST
from full90_capture_gates import validate_successor

PARENT = OUTPUT.parent/'full89-resource02/consumption-preparation-v2-dag'


def main():
    validate_successor()
    manifest = json.loads((OUTPUT/'capture-manifest.json').read_bytes())
    parent_receipt = json.loads((PARENT/'readiness.json').read_bytes())
    if digest(PARENT/'tooling.tar.gz') != parent_receipt['tooling_archive_sha256']:
        raise RuntimeError('Shared-DAG parent tooling changed')
    with tarfile.open(PARENT/'tooling.tar.gz', 'r:gz') as archive:
        files = {name: archive.extractfile(name).read() for name in archive.getnames()}
    if sha(files['probe.lean']) != '723D092CFA0B297600FF19039395ADF05645C5439863F6D62D2A3F5160668625':
        raise RuntimeError('Qualified shared-DAG probe changed')
    source = files['probe.lean'].decode('utf-8')
    match = re.search(r'private def roots : List String := (\[.*?\])', source)
    original_roots = json.loads(match.group(1))
    roots = manifest['requested_axioms']
    if len(original_roots) != 172 or roots != original_roots+[REQUEST] or len(set(roots)) != 173:
        raise RuntimeError('Original native172 or material root identity mismatch')
    modules = json.loads(re.search(r'private def projectModules : List String := (\[.*?\])', source).group(1))
    expected = {rel.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for rel in manifest['project_sources']}
    if len(modules) != 319 or set(modules) != expected:
        raise RuntimeError('Project module identity mismatch')
    source = source[:match.start(1)]+json.dumps(roots)+source[match.end(1):]
    files['probe.lean'] = source.encode('utf-8')
    postprocess = files['postprocess.py'].decode('utf-8')
    old = "'selected_leaf_failed_zoom_HC46_original']]"
    if postprocess.count(old) != 1:
        raise RuntimeError('Unexpected focused consumer selection')
    postprocess = postprocess.replace(old, "'selected_leaf_failed_zoom_HC46_original','selected_actual_material_moment_bound_original']]")
    old = 'assert len(roots)==172 and len(set(roots))==172 and len(focused)==4'
    if postprocess.count(old) != 1:
        raise RuntimeError('Unexpected parent root cardinality gate')
    postprocess = postprocess.replace(old, 'assert len(roots)==173 and len(set(roots))==173 and len(focused)==5')
    postprocess = postprocess.replace('focused-four-consumer', 'focused-five-consumer').replace('exact172-native', 'exact173-native')
    ast.parse(postprocess)
    files['postprocess.py'] = postprocess.encode('utf-8')
    spec = json.loads(files['preparation-status.json'])
    spec.update(status='Full90 exact173/focused-five tooling only; unexecuted; native qualification required first',
                roots=roots, graph_labels=['focused-five-consumer','exact173-native'], native_execution=False)
    files['preparation-status.json'] = (json.dumps(spec, indent=2)+'\n').encode()
    destination = OUTPUT/'consumption-preparation-v1-dag'
    destination.mkdir()
    with tarfile.open(destination/'tooling.tar.gz', 'w:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        (destination/name).write_bytes(data)
    receipt = {'schema': 'full90-expanded-material-consumption-preparation-v1',
               'parent_tooling_archive_sha256': digest(PARENT/'tooling.tar.gz'),
               'capture_manifest_sha256': digest(OUTPUT/'capture-manifest.json'),
               'input_archive_sha256': digest(OUTPUT/'input-archive.tar.gz'),
               'tooling_archive_sha256': digest(destination/'tooling.tar.gz'),
               'files': {name: {'sha256': sha(data), 'bytes': len(data)} for name, data in files.items()},
               'project_modules_exact': 319, 'requested_roots_exact': 173, 'focused_consumers_exact': 5,
               'original172_root_order_preserved': True, 'additional_root': REQUEST,
               'shared_DAG_algorithm_preserved': True, 'probe_executed': False,
               'native_green': False, 'consumption_coverage_complete': False,
               'reviewed': False, 'accepted': False, 'launch_clearance': False,
               'scope': 'Preparation only. Full90 native GREEN, exact custody and independent termination are prerequisites for a separately guarded GCP probe.'}
    (destination/'readiness.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'root': str(destination), 'roots': 173, 'focused': 5,
                      'tooling_sha256': receipt['tooling_archive_sha256'], 'probe_executed': False}))


if __name__ == '__main__':
    main()
