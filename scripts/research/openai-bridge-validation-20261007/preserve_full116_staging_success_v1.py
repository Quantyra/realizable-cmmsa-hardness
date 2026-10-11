"""Preserve exact successful Full116 staging, including complete transport streams."""
import hashlib,json,shutil,tarfile
from pathlib import Path
from custody_checks import digest
from full116_builder02_controller import ROOT
HERE=Path(__file__).resolve().parent
def main(original_handle):
    receipt,=(ROOT/'staging-controls').glob('*/staged.json')
    folder=receipt.parent;stage=json.loads(receipt.read_bytes())
    assert not stage['compiler_invoked'] and stage['full_frozen_remote_preflight_executed']
    assert stage['dependency_preflight']['project_sources_verified']==369
    assert stage['dependency_preflight']['gcp_identity']['id']=='7237681467779354904'
    for name,pin in stage['uploaded_sha256'].items():
        path=ROOT/name if (ROOT/name).is_file() else HERE/name
        assert digest(path)==pin
    wrappers=[]
    for candidate in (ROOT/'research-resume-20261011').iterdir():
        command_path=candidate/'command.json'
        if not command_path.is_file():continue
        entry=json.loads(command_path.read_bytes())
        if len(entry['argv'])>7 and Path(entry['argv'][7]).name=='stage_full116_openssh_v2.py':
            assert entry['native_exit']==0;wrappers.append(candidate)
    wrapper,=wrappers
    command=json.loads((wrapper/'command.json').read_bytes());assert command['native_exit']==0
    for stream in ('stdout','stderr'):assert digest(wrapper/stream)==command[stream+'_sha256']
    commands=json.loads((folder/'transport/commands.json').read_bytes())
    for i,row in enumerate(commands):
        assert row['native_exit']==0
        for stream in ('stdout','stderr'):assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
        if 'stdin_sha256' in row:assert digest(folder/'transport'/f'{i:03d}.stdin')==row['stdin_sha256']
    paths={p for root in (folder,wrapper) for p in root.rglob('*') if p.is_file()}
    paths.add(Path(__file__).resolve())
    assert shutil.disk_usage(HERE).free>=1803550720+8*1024**2
    target=HERE/'full116-staging-success-record-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    archive=target/'complete-originals.tar.gz';rows=[]
    with tarfile.open(archive,'x:gz',compresslevel=9) as tar:
        for i,p in enumerate(sorted(paths)):
            member=f'{i:03d}-'+p.name
            row=dict(original=str(p),member=member,bytes=p.stat().st_size,sha256=digest(p))
            tar.add(p,arcname=member,recursive=False);assert digest(p)==row['sha256'];rows.append(row)
    with tarfile.open(archive,'r:gz') as tar:
        assert len(tar.getmembers())==len(rows)
        for row in rows:
            data=tar.extractfile(row['member']).read()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256']
    index=dict(original_handle=original_handle,native_exit=0,originals=rows,
        files=[dict(copy=archive.name,bytes=archive.stat().st_size,sha256=digest(archive))],
        full_frozen_package_staged=True,every_original_member_roundtrip_verified=True,
        compiler_invoked=False,mathematical_acceptance=False)
    (target/'index.json').open('x').write(json.dumps(index,indent=2)+'\n')
    assert shutil.disk_usage(HERE).free>=1803550720
    print(json.dumps(dict(folder=str(target),complete_originals=len(rows),archive_sha256=digest(archive))),flush=True)
if __name__=='__main__':
    import sys
    main(int(sys.argv[1]))

