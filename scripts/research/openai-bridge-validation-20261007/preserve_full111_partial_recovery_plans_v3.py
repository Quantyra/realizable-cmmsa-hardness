"""Keep all four completed plans and the unmodified scope99 capacity failure."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest
from full111_builder02_controller import ROOT
from full112_builder02_controller import ROOT as NEXT

HERE=Path(__file__).resolve().parent


def main():
    folder=ROOT/'settled-cache-recovery-v2/openssh-plan-20261011T044730710232Z'
    wrapper=NEXT/'research-resume-20261011/20261011T044607572150Z-1fdee324a245'
    command=json.loads((wrapper/'command.json').read_bytes());assert command['native_exit']==1
    for stream in ('stdout','stderr'):assert digest(wrapper/stream)==command[stream+'_sha256']
    commands=json.loads((folder/'transport/commands.json').read_bytes())
    assert [i for i,r in enumerate(commands) if r['native_exit']!=0]==[14]
    assert commands[14]['native_exit']==1 and commands[-1]['argv'][0]=='taskkill.exe'
    for row in commands:
        for stream in ('stdout','stderr'):assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
    assert 'Insufficient identical dependency-object copies; no changes made' in (folder/'transport/014.stderr').read_text()
    operations=[]
    for n in (111,96,97,98):
        row=json.loads((folder/f'operation-{n}.json').read_bytes());p=Path(row['local_result'])
        assert row['action']=='plan' and digest(p)==row['result_sha256']
        plan=json.loads(p.read_bytes());assert not plan['executed']
        operations.append(dict(number=n,rows=len(plan['rows']),allocated_bytes=plan['allocated_bytes'],sha256=digest(p)))
    assert not (folder/'result.json').exists()
    paths={p for root in (folder,wrapper) for p in root.rglob('*') if p.is_file()}
    paths.update([Path(__file__).resolve(),HERE/'full111-settled-cache-recovery-derivation-v2.json'])
    assert shutil.disk_usage(HERE).free>=1536*1024**2+16*1024**2
    target=HERE/'full111-four-plans-scope99-failure-record-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    archive=target/'complete-originals.tar.gz';rows=[]
    with tarfile.open(archive,'x:gz',compresslevel=9) as tar:
        for i,p in enumerate(sorted(paths)):
            name=f'{i:03d}-'+p.name;row=dict(original=str(p),member=name,bytes=p.stat().st_size,sha256=digest(p))
            tar.add(p,arcname=name,recursive=False);assert digest(p)==row['sha256'];rows.append(row)
    with tarfile.open(archive,'r:gz') as tar:
        assert len(tar.getmembers())==len(rows)
        for row in rows:
            data=tar.extractfile(row['member']).read()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest().upper()==row['sha256']
    assert shutil.disk_usage(HERE).free>=1536*1024**2
    (target/'index.json').open('x').write(json.dumps(dict(original_handle=69502,original_exit=1,
        originals=rows,files=[dict(copy=archive.name,bytes=archive.stat().st_size,sha256=digest(archive))],
        completed_plans=operations,failed_scope=99,unattempted_scopes=[100,101],
        no_cache_execution_invoked=True,every_archive_member_roundtrip_verified=True,
        last_scope99_progress=json.loads((folder/'transport/014.stdout').read_text().splitlines()[-1]),
        last_progress_not_final_total=True,compiler_invoked=False,accepted=False),indent=2)+'\n')
    print(json.dumps(dict(folder=str(target),complete_originals=len(rows),archive_sha256=digest(archive),completed_plans=operations)),flush=True)


if __name__=='__main__':main()
