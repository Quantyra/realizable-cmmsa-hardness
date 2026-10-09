"""Prepare complete additive trace tooling without Lean or GCP execution."""
import io
import json
import re
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full101 import OUTPUT, PARENT, additions


def main():
    parent = PARENT / 'consumption-preparation-v1-dag'
    old = json.loads((parent / 'readiness.json').read_bytes())
    assert digest(parent / 'tooling.tar.gz') == old['tooling_archive_sha256'] == '46304DF40EADB59BE5D234FB91C9B31355AFFC9BA7866851D5613D85D18514E7'
    a = json.loads((PARENT / 'capture-manifest.json').read_bytes())
    b = json.loads((OUTPUT / 'capture-manifest.json').read_bytes())
    sources, requests = additions()
    assert list(b['project_sources']) == list(a['project_sources']) + list(sources)
    assert b['requested_axioms'] == a['requested_axioms'] + requests
    with tarfile.open(parent / 'tooling.tar.gz') as archive:
        members = archive.getmembers()
        assert all(m.isfile() for m in members) and len({m.name for m in members}) == len(members)
        files = {m.name: archive.extractfile(m).read() for m in members}
    for name, row in old['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    spec = json.loads(files['preparation-status.json'])
    assert spec['roots'] == a['requested_axioms'] and len(spec['focused_roots']) == 24
    modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in b['project_sources']]
    added_modules = [p.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for p in sources]
    probe = files['probe.lean'].decode('utf-8')
    original_probe = probe
    replacements = []
    for field, expected, value in [('projectModules', modules[:327], modules), ('roots', a['requested_axioms'], b['requested_axioms'])]:
        pattern = r'(private def ' + field + r' : List String := )(\[.*?\])'
        found = re.search(pattern, probe)
        assert found and json.loads(found.group(2)) == expected
        replacement = json.dumps(value)
        probe = probe[:found.start(2)] + replacement + probe[found.end(2):]
        replacements.append((json.dumps(value), found.group(2)))
    # Only imports and the two exact data lists change, not the traversal/type-DAG algorithm.
    recovered_algorithm = probe
    for new, previous in reversed(replacements):
        assert recovered_algorithm.count(new) == 1
        recovered_algorithm = recovered_algorithm.replace(new, previous, 1)
    assert recovered_algorithm == original_probe
    files['probe.lean'] = (''.join('import ' + m + '\n' for m in added_modules) + probe).encode('utf-8')
    spec.update(status='Full101 full251/focused83 tooling; native qualification required',
                roots=b['requested_axioms'], project_modules=modules,
                focused_roots=spec['focused_roots'] + requests,
                graph_labels=['focused-eighty-three-consumer', 'exact251-native'])
    assert len(spec['roots']) == 251 and len(set(spec['focused_roots'])) == 83 and len(modules) == 340
    files['preparation-status.json'] = (json.dumps(spec, indent=2) + '\n').encode()
    root = OUTPUT / 'consumption-preparation-v1-dag'
    root.mkdir()
    with tarfile.open(root / 'tooling.tar.gz', 'x:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name)
            member.size, member.mode = len(data), 0o644
            archive.addfile(member, io.BytesIO(data))
    for name, data in files.items():
        with (root / name).open('xb') as stream:
            stream.write(data)
    report = dict(old, schema='full101-complete251-focused83-preparation-v1',
        parent_tooling_archive_sha256=digest(parent / 'tooling.tar.gz'),
        capture_manifest_sha256=digest(OUTPUT / 'capture-manifest.json'),
        input_archive_sha256=digest(OUTPUT / 'input-archive.tar.gz'),
        tooling_archive_sha256=digest(root / 'tooling.tar.gz'),
        files={name: dict(sha256=sha(data), bytes=len(data)) for name, data in files.items()},
        project_modules_exact=340, requested_roots_exact=251, focused_consumers_exact=83,
        additional_roots=requests, focused_roots=spec['focused_roots'],
        all192_parent_roots_and24_parent_focus_preserved=True,
        identical_probe_and_postprocess_bytes=False, identical_postprocess_bytes=True,
        probe_algorithm_exact_inverse_reconstruction=True,
        probe_executed=False, native_qualification_pending=True, launch_clearance=False, accepted=False)
    with (root / 'readiness.json').open('xb') as stream:
        stream.write((json.dumps(report, indent=2) + '\n').encode())
    print(json.dumps(dict(tooling_sha256=report['tooling_archive_sha256'], roots=251, focused=83,
                         modules=340, probe_executed=False)))


if __name__ == '__main__':
    main()
