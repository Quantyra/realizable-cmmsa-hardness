"""Freeze full257/focused89 tooling; no compiler or cloud operation."""
import io
import json
import re
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full105 import OUTPUT
from prepare_builder02_full103 import OUTPUT as PARENT
from prepare_full104_consumer_energy_scope import additions
from pathlib import Path


def main():
    parent = PARENT/'consumption-preparation-v1-dag'
    old = json.loads((parent/'readiness.json').read_bytes())
    assert digest(parent/'tooling.tar.gz') == old['tooling_archive_sha256']
    a, b = [json.loads((root/'capture-manifest.json').read_bytes()) for root in [PARENT, OUTPUT]]
    sources, requests = additions()
    assert list(b['project_sources']) == list(a['project_sources'])+list(sources)
    assert b['requested_axioms'] == a['requested_axioms']+requests
    with tarfile.open(parent/'tooling.tar.gz') as archive:
        members = archive.getmembers()
        assert len(members) == 3 and all(m.isfile() for m in members)
        files = {m.name:archive.extractfile(m).read() for m in members}
    for name, row in old['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    spec = json.loads(files['preparation-status.json'])
    assert spec['roots'] == a['requested_axioms'] and len(spec['focused_roots']) == 83
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in b['project_sources']]
    probe = files['probe.lean'].decode('utf-8')
    previous = probe
    replacements = []
    for field, expected, value in [('projectModules', modules[:340], modules), ('roots', a['requested_axioms'], b['requested_axioms'])]:
        found = re.search(r'(private def '+field+r' : List String := )(\[.*?\])', probe)
        assert found and json.loads(found.group(2)) == expected
        replacement = json.dumps(value)
        probe = probe[:found.start(2)]+replacement+probe[found.end(2):]
        replacements.append((replacement, found.group(2)))
    inverse = probe
    for changed, original in reversed(replacements):
        assert inverse.count(changed) == 1
        inverse = inverse.replace(changed, original, 1)
    assert inverse == previous
    added_modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in sources]
    files['probe.lean'] = (''.join('import '+module+'\n' for module in added_modules)+probe).encode()
    post = Path(__file__).with_name('full103_trace_postprocess_scope_v3.py').read_bytes()
    assert post.count(b'==251') == 2 and post.count(b'==83') == 1
    files['postprocess.py'] = post.replace(b'==251', b'==257').replace(b'==83', b'==89').replace(
        b'exact251-native', b'exact257-native').replace(b'focused-eighty-three-consumer', b'focused-eighty-nine-consumer')
    inverse_post = files['postprocess.py'].replace(b'==257', b'==251').replace(b'==89', b'==83').replace(
        b'exact257-native', b'exact251-native').replace(b'focused-eighty-nine-consumer', b'focused-eighty-three-consumer')
    assert inverse_post == post
    spec.update(status='Full105 full257/focused89 tooling; actual qualified native required',
        roots=b['requested_axioms'], project_modules=modules, focused_roots=spec['focused_roots']+requests,
        graph_labels=['focused-eighty-nine-consumer', 'exact257-native'])
    assert len(modules) == 344 and len(set(spec['roots'])) == 257 and len(set(spec['focused_roots'])) == 89
    files['preparation-status.json'] = (json.dumps(spec, indent=2)+'\n').encode()
    root = OUTPUT/'consumption-preparation-v1-dag'
    root.mkdir()
    with tarfile.open(root/'tooling.tar.gz', 'x:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        (root/name).open('xb').write(data)
    result = dict(old, schema='full105-complete257-focused89-preparation-v1',
        parent_tooling_archive_sha256=digest(parent/'tooling.tar.gz'),
        capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'), input_archive_sha256=digest(OUTPUT/'input-archive.tar.gz'),
        tooling_archive_sha256=digest(root/'tooling.tar.gz'),
        files={name:dict(sha256=sha(data), bytes=len(data)) for name,data in files.items()},
        project_modules_exact=344, requested_roots_exact=257, focused_consumers_exact=89,
        additional_roots=requests, focused_roots=spec['focused_roots'],
        all251_parent_roots_and83_parent_focus_preserved=True,
        identical_probe_and_postprocess_bytes=False, identical_postprocess_bytes=False,
        probe_algorithm_exact_inverse_reconstruction=True, postprocess_algorithm_exact_inverse_reconstruction=True,
        postprocess_cardinality_guards_match_expanded_scope=True,
        probe_executed=False, native_qualification_pending=True, launch_clearance=False, accepted=False)
    (root/'readiness.json').open('xb').write((json.dumps(result, indent=2)+'\n').encode())
    print(json.dumps(dict(tooling_sha256=result['tooling_archive_sha256'], roots=257, focused=89, modules=344, probe_executed=False)))


if __name__ == '__main__':
    main()
