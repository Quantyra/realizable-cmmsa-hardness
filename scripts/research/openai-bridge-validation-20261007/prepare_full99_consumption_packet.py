"""Rebind full192/focused24 tooling to the syntax-only Full99 capture."""
import io
import json
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full99 import OUTPUT, PARENT
from full99_capture_gates import validate_successor

def main():
    validate_successor()
    parent = PARENT/'consumption-preparation-v1-dag'
    old = json.loads((parent/'readiness.json').read_bytes())
    assert digest(parent/'tooling.tar.gz') == old['tooling_archive_sha256'] == '7309044159042A6B7744F404AFD3A7CF5B97E501AD5F51E9362D43092FA0F1CC'
    a = json.loads((PARENT/'capture-manifest.json').read_bytes())
    b = json.loads((OUTPUT/'capture-manifest.json').read_bytes())
    assert a['requested_axioms'] == b['requested_axioms'] and len(b['requested_axioms']) == 192
    assert list(a['project_sources']) == list(b['project_sources']) and len(b['project_sources']) == 327
    with tarfile.open(parent/'tooling.tar.gz') as archive:
        files = {m.name:archive.extractfile(m).read() for m in archive.getmembers()}
    for name,row in old['files'].items():
        assert sha(files[name]) == row['sha256'] and len(files[name]) == row['bytes']
    spec = json.loads(files['preparation-status.json'])
    assert spec['roots'] == b['requested_axioms'] and len(set(spec['focused_roots'])) == 24
    spec['status'] = 'Full99 full192/focused24 tooling; native qualification required'
    files['preparation-status.json'] = (json.dumps(spec,indent=2)+'\n').encode()
    root = OUTPUT/'consumption-preparation-v1-dag'; root.mkdir()
    with tarfile.open(root/'tooling.tar.gz','x:gz') as archive:
        for name,data in sorted(files.items()):
            member = tarfile.TarInfo(name); member.size=len(data); member.mode=0o644
            archive.addfile(member,io.BytesIO(data))
    for name,data in files.items(): (root/name).write_bytes(data)
    report = dict(old, schema='full99-complete192-focused24-preparation-v1',
        parent_tooling_archive_sha256=digest(parent/'tooling.tar.gz'),
        capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'),
        input_archive_sha256=digest(OUTPUT/'input-archive.tar.gz'),
        tooling_archive_sha256=digest(root/'tooling.tar.gz'),
        files={name:dict(sha256=sha(data),bytes=len(data)) for name,data in files.items()},
        identical_probe_and_postprocess_bytes=True, probe_executed=False,
        native_qualification_pending=True, launch_clearance=False, accepted=False)
    (root/'readiness.json').write_bytes((json.dumps(report,indent=2)+'\n').encode())
    print(json.dumps({'tooling_sha256':report['tooling_archive_sha256'],'roots':192,'focused':24,'modules':327,'probe_executed':False}))

if __name__ == '__main__': main()
