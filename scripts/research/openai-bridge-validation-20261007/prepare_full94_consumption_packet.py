"""Prepare exact181 roots/323 modules, preserving qualified shared-DAG logic."""
import ast
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full94 import OUTPUT
from prepare_builder02_full91 import PARENT, REQUESTS as SIZE_REQUESTS
from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS, MODULE
from prepare_builder02_full92 import MODULES
REQUESTS = SIZE_REQUESTS + DYADIC_REQUESTS
IMPORTS = ''.join('import ' + name + '\n' for name in MODULES + [MODULE]).encode()
from full94_capture_gates import validate_successor


def main():
    validate_successor()
    parent = PARENT / 'consumption-preparation-v1-dag'
    readiness = json.loads((parent / 'readiness.json').read_bytes())
    assert digest(parent / 'tooling.tar.gz') == readiness['tooling_archive_sha256'] == 'B70104313F3D23EDB7A58C00B4479B73496D8349E60AF01460BF3C43CB0A9A33'
    with tarfile.open(parent / 'tooling.tar.gz', 'r:gz') as archive:
        files = {n: archive.extractfile(n).read() for n in archive.getnames()}
    for name, row in readiness['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    manifest = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    old_manifest = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    roots = manifest['requested_axioms']
    assert roots == old_manifest['requested_axioms'] + REQUESTS and len(roots) == len(set(roots)) == 181
    source = files['probe.lean'].decode()
    old_source = source
    replacements = []
    for field, expected, added in [
        ('roots', old_manifest['requested_axioms'], roots),
        ('projectModules', [rel.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for rel in old_manifest['project_sources']],
         [rel.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for rel in manifest['project_sources']]),
    ]:
        match = re.search(r'private def ' + field + r' : List String := (\[.*?\])', source)
        assert match is not None
        original = match.group(1)
        assert set(json.loads(original)) == set(expected)
        if field == 'roots':
            assert json.loads(original) == expected
        successor = json.dumps(added)
        source = source[:match.start(1)] + successor + source[match.end(1):]
        replacements.append((successor, original))
    inverse = source
    for successor, original in reversed(replacements):
        assert inverse.count(successor) == 1
        inverse = inverse.replace(successor, original, 1)
    assert inverse == old_source, 'Shared-DAG algorithm changed'
    files['probe.lean'] = IMPORTS + source.encode()
    assert files['probe.lean'][len(IMPORTS):].decode() == source
    post = files['postprocess.py'].decode()
    line = next(line for line in post.splitlines() if line.startswith("roots=spec['roots']; focused="))
    original_focused = [n for n in old_manifest['requested_axioms'] if n.rsplit('.', 1)[-1] in [
        'manuscript_A22_actual', 'original_HC46_exact', 'selected_leaf_HC46_original',
        'selected_leaf_failed_zoom_HC46_original', 'selected_actual_material_moment_bound_original']]
    assert len(original_focused) == 5
    focused = original_focused + REQUESTS
    post = post.replace(line, "roots=spec['roots']; focused=spec['focused_roots']")
    guard = 'assert len(roots)==173 and len(set(roots))==173 and len(focused)==5'
    assert post.count(guard) == 1
    post = post.replace(guard, 'assert len(roots)==181 and len(set(roots))==181 and len(focused)==len(set(focused))==13 and set(focused)<=set(roots)')
    post = post.replace('focused-five-consumer', 'focused-thirteen-consumer').replace('exact173-native', 'exact181-native')
    ast.parse(post)
    files['postprocess.py'] = post.encode()
    spec = json.loads(files['preparation-status.json'])
    spec.update(status='Full94 exact181/focused-thirteen preparation only; no probe execution',
                roots=roots, focused_roots=focused, graph_labels=['focused-thirteen-consumer', 'exact181-native'], native_execution=False)
    files['preparation-status.json'] = (json.dumps(spec, indent=2) + '\n').encode()
    destination = OUTPUT / 'consumption-preparation-v1-dag'
    destination.mkdir()
    with tarfile.open(destination / 'tooling.tar.gz', 'x:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        (destination / name).write_bytes(data)
    receipt = {'schema': 'full94-additive-consumption-preparation-v1',
               'parent_tooling_archive_sha256': digest(parent / 'tooling.tar.gz'),
               'capture_manifest_sha256': digest(OUTPUT / 'capture-manifest.json'),
               'input_archive_sha256': digest(OUTPUT / 'input-archive.tar.gz'),
               'tooling_archive_sha256': digest(destination / 'tooling.tar.gz'),
               'files': {name: {'sha256': sha(data), 'bytes': len(data)} for name, data in files.items()},
               'project_modules_exact': 323, 'requested_roots_exact': 181, 'focused_consumers_exact': 13,
               'original173_root_order_preserved': True, 'additional_roots': REQUESTS,
               'focused_roots': focused, 'shared_DAG_algorithm_inverse_parity': True, 'added_imports': MODULES + [MODULE],
               'probe_executed': False, 'native_qualification_pending': True,
               'consumption_coverage_complete': False, 'accepted': False, 'launch_clearance': False}
    (destination / 'readiness.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'root': str(destination), 'roots': 181, 'focused': 13,
                      'modules': 323, 'tooling_sha256': receipt['tooling_archive_sha256'], 'probe_executed': False}))


if __name__ == '__main__':
    main()
