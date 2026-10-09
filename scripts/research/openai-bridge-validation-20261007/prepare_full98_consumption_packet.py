"""Prepare all192 roots/all327 modules; no compiler or cloud operation."""
import ast
import io
import json
import re
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full98 import OUTPUT, PARENT, NEW_REQUESTS, MODULES
from full98_capture_gates import validate_successor

PARENT_TOOLING = '8723A7A8D472EC4CBF8F7649D58E4EB80E0E2505D219430FFC3C22D63DA1714C'

def main():
    validate_successor()
    parent = PARENT / 'consumption-preparation-v1-dag'
    readiness = json.loads((parent / 'readiness.json').read_bytes())
    assert digest(parent / 'tooling.tar.gz') == readiness['tooling_archive_sha256'] == PARENT_TOOLING
    old = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    new = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    assert new['requested_axioms'] == old['requested_axioms'] + NEW_REQUESTS
    assert len(new['requested_axioms']) == 192 and len(new['project_sources']) == 327
    with tarfile.open(parent / 'tooling.tar.gz') as archive:
        files = {m.name: archive.extractfile(m).read() for m in archive.getmembers()}
    for name, row in readiness['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    original = files['probe.lean'].decode('utf-8')
    source = original
    replacements = []
    for field, before_values, after_values in [
        ('roots', old['requested_axioms'], new['requested_axioms']),
        ('projectModules', [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in old['project_sources']],
         [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in new['project_sources']])]:
        match = re.search(r'private def ' + field + r' : List String := (\[.*?\])', source)
        assert match and json.loads(match.group(1)) == before_values
        before, after = match.group(1), json.dumps(after_values)
        source = source[:match.start(1)] + after + source[match.end(1):]
        replacements.append((before, after))
    inverse = source
    for before, after in reversed(replacements):
        assert inverse.count(after) == 1
        inverse = inverse.replace(after, before, 1)
    assert inverse == original
    files['probe.lean'] = ''.join('import ' + m + '\n' for m in MODULES).encode() + source.encode('utf-8')
    original_post = files['postprocess.py'].decode()
    guard = 'assert len(roots)==184 and len(set(roots))==184 and len(focused)==len(set(focused))==16 and set(focused)<=set(roots)'
    new_guard = 'assert len(roots)==192 and len(set(roots))==192 and len(focused)==len(set(focused))==24 and set(focused)<=set(roots)'
    assert original_post.count(guard) == 1
    post = original_post.replace(guard, new_guard).replace('focused-sixteen-consumer', 'focused-twentyfour-consumer').replace('exact184-native', 'exact192-native')
    assert post.replace(new_guard, guard).replace('focused-twentyfour-consumer', 'focused-sixteen-consumer').replace('exact192-native', 'exact184-native') == original_post
    ast.parse(post)
    files['postprocess.py'] = post.encode()
    spec = json.loads(files['preparation-status.json'])
    assert spec['roots'] == old['requested_axioms'] and len(spec['focused_roots']) == 16
    spec.update(status='Full98 full192/focused24 tooling; native qualification required',
                roots=new['requested_axioms'], focused_roots=spec['focused_roots'] + NEW_REQUESTS,
                graph_labels=['focused-twentyfour-consumer', 'exact192-native'])
    assert len(set(spec['focused_roots'])) == 24 and set(spec['focused_roots']) <= set(spec['roots'])
    files['preparation-status.json'] = (json.dumps(spec, indent=2) + '\n').encode()
    root = OUTPUT / 'consumption-preparation-v1-dag'
    root.mkdir()
    with tarfile.open(root / 'tooling.tar.gz', 'x:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        (root / name).write_bytes(data)
    report = dict(schema='full98-complete192-focused24-preparation-v1',
        parent_tooling_archive_sha256=PARENT_TOOLING,
        capture_manifest_sha256=digest(OUTPUT / 'capture-manifest.json'),
        input_archive_sha256=digest(OUTPUT / 'input-archive.tar.gz'),
        tooling_archive_sha256=digest(root / 'tooling.tar.gz'),
        files={name: {'sha256': sha(data), 'bytes': len(data)} for name, data in files.items()},
        project_modules_exact=327, requested_roots_exact=192, focused_consumers_exact=24,
        original184_root_order_preserved=True, additional_roots=readiness['additional_roots'] + NEW_REQUESTS,
        focused_roots=spec['focused_roots'], shared_DAG_algorithm_inverse_parity=True,
        probe_executed=False, native_qualification_pending=True, accepted=False, launch_clearance=False)
    (root / 'readiness.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'roots': 192, 'focused': 24, 'modules': 327,
                      'tooling_sha256': report['tooling_archive_sha256'], 'probe_executed': False}))

if __name__ == '__main__':
    main()
