"""Reuse identical full-scope probe algorithm for the warning-only capture."""
import io
import json
import tarfile
from custody_checks import digest
from prepare_builder02 import sha
from prepare_builder02_full103 import OUTPUT,PARENT


def main():
    parent=PARENT/'consumption-preparation-v1-dag';r=json.loads((parent/'readiness.json').read_bytes())
    assert digest(parent/'tooling.tar.gz')==r['tooling_archive_sha256']
    old=json.loads((PARENT/'capture-manifest.json').read_bytes());new=json.loads((OUTPUT/'capture-manifest.json').read_bytes())
    assert old['requested_axioms']==new['requested_axioms'] and list(old['project_sources'])==list(new['project_sources'])
    assert r['requested_roots_exact']==251 and r['focused_consumers_exact']==83 and r['project_modules_exact']==340
    with tarfile.open(parent/'tooling.tar.gz') as archive:
        files={m.name:archive.extractfile(m).read() for m in archive.getmembers()}
    for name,row in r['files'].items():assert sha(files[name])==row['sha256'] and len(files[name])==row['bytes']
    status=json.loads(files['preparation-status.json'])
    assert status['roots']==new['requested_axioms'] and len(set(status['focused_roots']))==83
    status['status']='Full103 full251/focused83 tooling; actual native qualification required'
    files['preparation-status.json']=(json.dumps(status,indent=2)+'\n').encode()
    root=OUTPUT/'consumption-preparation-v1-dag';root.mkdir()
    with tarfile.open(root/'tooling.tar.gz','x:gz') as archive:
        for name,data in sorted(files.items()):
            m=tarfile.TarInfo(name);m.size=len(data);m.mode=0o644;archive.addfile(m,io.BytesIO(data))
    for name,data in files.items():(root/name).write_bytes(data)
    result=dict(r,schema='full103-complete251-focused83-preparation-v1',
                parent_tooling_archive_sha256=digest(parent/'tooling.tar.gz'),
                capture_manifest_sha256=digest(OUTPUT/'capture-manifest.json'),input_archive_sha256=digest(OUTPUT/'input-archive.tar.gz'),
                tooling_archive_sha256=digest(root/'tooling.tar.gz'),files={name:dict(sha256=sha(data),bytes=len(data)) for name,data in files.items()},
                identical_probe_and_postprocess_bytes=True,probe_executed=False,native_qualification_pending=True,accepted=False)
    (root/'readiness.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(tooling_sha256=result['tooling_archive_sha256'],roots=251,focused=83,modules=340,native_run_binding_pending=True)))


if __name__=='__main__':main()
