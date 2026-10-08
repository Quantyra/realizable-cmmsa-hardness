"""Prepare a separately bound Full83 capsule; never invoke a compiler."""
import hashlib
import io
import json
from pathlib import Path
import tarfile

CAPTURE = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/docs/a8-gcp/r1007/captures/capture-full-a22-hc46-83')
OUTPUT = Path('C:/Users/dfred/.quantyra/builder02/full83-resource02')
OLD_ID = '8337954477286097405'
NEW_ID = '7237681467779354904'
PINS = {'manifest.json':'AEB36ED4DA0D9CED89A0B3D070F7B2ED40D70A7D06CA1589115C526EB981BE5C', 'input-archive.tar.gz':'E5BFA192CF76DAC732391B412E4E84B926DE13605DEE33F12AA25FCE7BD08F49'}

def sha(data): return hashlib.sha256(data).hexdigest().upper()

def prepare():
    for name, expected in PINS.items():
        if sha((CAPTURE/name).read_bytes()) != expected: raise RuntimeError('Frozen capture drift')
    with tarfile.open(CAPTURE/'input-archive.tar.gz','r:gz') as source:
        members = source.getmembers()
        if any(not m.isfile() for m in members): raise RuntimeError('Non-file capsule entry')
        files = {m.name:source.extractfile(m).read() for m in members}
        if len(files) != len(members): raise RuntimeError('Duplicate capsule entries')
    before = dict(files)
    manifest = json.loads(files['capture-manifest.json'])
    if manifest['vm'] != 'quantyra-lean-builder-01': raise RuntimeError('Unexpected parent VM')
    manifest['vm'] = 'quantyra-lean-builder-02'
    files['capture-manifest.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    helper = files['cloud_capture.py']
    if helper.count(OLD_ID.encode()) != 1: raise RuntimeError('Unexpected host guard count')
    files['cloud_capture.py'] = helper.replace(OLD_ID.encode(),NEW_ID.encode())
    changed = sorted(k for k in files if files[k] != before[k])
    if changed != ['capture-manifest.json','cloud_capture.py']: raise RuntimeError('Unapproved capsule change')
    parent_manifest = json.loads(before['capture-manifest.json'])
    if {**manifest,'vm':parent_manifest['vm']} != parent_manifest: raise RuntimeError('Manifest changed beyond VM binding')
    for rel,row in manifest['project_sources'].items():
        if sha(files[rel]) != row['sha256']: raise RuntimeError('Project source drift: '+rel)
    for rel,row in manifest['configs'].items():
        if sha(files[rel]) != row['sha256']: raise RuntimeError('Config drift: '+rel)
    OUTPUT.mkdir(parents=True,exist_ok=False)
    with tarfile.open(OUTPUT/'input-archive.tar.gz','w:gz') as target:
        for name,data in sorted(files.items()):
            item = tarfile.TarInfo(name); item.size=len(data); item.mode=0o644
            target.addfile(item,io.BytesIO(data))
    (OUTPUT/'capture-manifest.json').write_bytes(files['capture-manifest.json'])
    receipt = dict(parent_capture=str(CAPTURE),parent_pins=PINS,vm=manifest['vm'],vm_id=NEW_ID,
        changed_files=changed,project_sources_preserved=len(manifest['project_sources']),
        all_other_capsule_files_preserved=True,compiler_invoked=False,launch_clearance=False,
        files={name:sha((OUTPUT/name).read_bytes()) for name in ['input-archive.tar.gz','capture-manifest.json']},
        helper_sha256=sha(files['cloud_capture.py']),parent_helper_sha256=sha(helper))
    (OUTPUT/'resource-binding.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__': prepare()
