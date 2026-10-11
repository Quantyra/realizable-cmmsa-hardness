"""Preserve complete seven-scope plan originals as a roundtrip-verified archive."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest
from run_full111_settled_cache_openssh_v3 import RECOVERY, NUMBERS
from full112_builder02_controller import ROOT as NEXT

HERE=Path(__file__).resolve().parent


def main():
    result_path,=RECOVERY.glob('openssh-plan-*/result.json')
    folder=result_path.parent
    result=json.loads(result_path.read_bytes())
    assert result['original_operations_settled'] and not result['compiler_invoked']
    assert [r['number'] for r in result['operations']]==NUMBERS
    wrapper=NEXT/'research-resume-20261011/20261011T044607572150Z-1fdee324a245'
    command=json.loads((wrapper/'command.json').read_bytes());assert command['native_exit']==0
    for stream in ('stdout','stderr'):assert digest(wrapper/stream)==command[stream+'_sha256']
    transport=folder/'transport'
    for row in json.loads((transport/'commands.json').read_bytes()):
        assert row['native_exit']==0
        for stream in ('stdout','stderr'):assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
    scopes=json.loads((HERE/'full111-settled-cache-recovery-derivation-v2.json').read_bytes())['scopes']
    summaries=[]
    for scope,record in zip(scopes,result['operations']):
        assert record['action']=='plan' and record['number']==scope['number']
        p=Path(record['local_result']);assert digest(p)==record['result_sha256']
        value=json.loads(p.read_bytes())
        assert not value['executed'] and not value['compiler_invoked']
        assert value['original_archive_sha256']==scope['archive_sha256']
        assert record['helper_sha256']==scope['helper_sha256']==digest(folder/scope['helper'])
        assert sum(r['allocated_bytes'] for r in value['rows'])==value['allocated_bytes']>=scope['target_bytes']
        summaries.append(dict(number=scope['number'],rows=len(value['rows']),allocated_bytes=value['allocated_bytes'],sha256=digest(p)))
    paths={p for root in (folder,wrapper) for p in root.rglob('*') if p.is_file()}
    paths.update([Path(__file__).resolve(),HERE/'full111-settled-cache-recovery-derivation-v2.json'])
    assert shutil.disk_usage(HERE).free>=1536*1024**2+16*1024**2
    target=HERE/'full111-recovery-plans-openssh-record-v3';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    archive=target/'complete-originals.tar.gz';rows=[]
    with tarfile.open(archive,'x:gz',compresslevel=9) as tar:
        for n,p in enumerate(sorted(paths)):
            member=f'{n:03d}-'+p.name
            row=dict(original=str(p),member=member,bytes=p.stat().st_size,sha256=digest(p))
            tar.add(p,arcname=member,recursive=False);assert digest(p)==row['sha256'];rows.append(row)
    with tarfile.open(archive,'r:gz') as tar:
        assert len(tar.getmembers())==len(rows)
        for row in rows:
            data=tar.extractfile(row['member']).read()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256']
            assert digest(Path(row['original']))==row['sha256']
    assert shutil.disk_usage(HERE).free>=1536*1024**2
    files=[dict(copy=archive.name,bytes=archive.stat().st_size,sha256=digest(archive))]
    (target/'index.json').open('x').write(json.dumps(dict(files=files,originals=rows,scopes=summaries,
        original_handle=69502,original_exit=0,all_seven_plans_verified=True,execution_included=False,
        every_original_archive_member_roundtrip_verified=True,compiler_invoked=False,mathematical_acceptance=False),indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),complete_originals=len(rows),archive_sha256=digest(archive),scopes=summaries)),flush=True)


if __name__=='__main__':main()
