"""Preserve complete eight-scope execution and independent audit, retaining plan custody."""
import hashlib,json,shutil,tarfile
from pathlib import Path
from custody_checks import digest
from audit_full111_settled_cache_recovery_v4 import AUDIT, RECOVERY, NUMBERS, validate_local_audit, unique_operation
from full112_builder02_controller import ROOT as NEXT
HERE=Path(__file__).resolve().parent

def main():
    audit=validate_local_audit()
    assert not (NEXT/'launch-once.json').exists()
    execution={unique_operation(n,'execute')[0].parent for n in NUMBERS}
    assert len(execution)==1
    folder=execution.pop()
    result=json.loads((folder/'result.json').read_bytes())
    assert result['original_operations_settled'] and [r['number'] for r in result['operations']]==NUMBERS
    once=RECOVERY/'execution-request-once-v2.json'
    assert json.loads(once.read_bytes())['control']==str(folder)
    previous=HERE/'full111-recovery-plans-openssh-record-v5/index.json'
    previous_value=json.loads(previous.read_bytes())
    assert previous_value['all_eight_plans_verified'] and not previous_value['execution_included']
    assert json.loads(once.read_bytes())['plan_custody_sha256']==digest(previous)
    for r in previous_value['files']:
        assert digest(previous.parent/r['copy'])==r['sha256']
    paths={Path(__file__).resolve(),once,previous,HERE/'full111-settled-cache-recovery-derivation-v4.json'}
    wrappers=[]
    for p in (NEXT/'research-resume-20261011').glob('*/command.json'):
        row=json.loads(p.read_bytes())
        name=Path(row['argv'][7]).name
        if (name=='run_full111_settled_cache_openssh_v5.py' and row['argv'][8:]==['execute']) or name in ('audit_full111_settled_cache_recovery_v4.py','preserve_full111_complete_recovery_plans_v5.py'):
            assert row['native_exit']==0
            for stream in ('stdout','stderr'):assert digest(p.parent/stream)==row[stream+'_sha256']
            assert digest(p.parent/name)==row['source_sha256']
            paths.update(q for q in p.parent.rglob('*') if q.is_file())
            wrappers.append(dict(folder=str(p.parent),action=name,native_exit=0))
    assert len(wrappers)==3
    for root in (folder,AUDIT):
        commands=json.loads((root/'transport/commands.json').read_bytes())
        assert commands and all(r['native_exit']==0 for r in commands)
        assert commands[-1]['argv'][0]=='taskkill.exe'
        for i,row in enumerate(commands):
            for stream in ('stdout','stderr'):assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
            if 'stdin_sha256' in row:assert digest(root/'transport'/f'{i:03d}.stdin')==row['stdin_sha256']
        paths.update(p for p in root.rglob('*') if p.is_file())
    assert shutil.disk_usage(HERE).free>=1536*1024**2+32*1024**2
    target=HERE/'full111-complete-recovery-record-v4';target.mkdir(exist_ok=False)
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
            with tar.extractfile(row['member']) as stream:
                assert hashlib.file_digest(stream,'sha256').hexdigest().upper()==row['sha256']
            assert tar.getmember(row['member']).size==row['bytes'] and digest(Path(row['original']))==row['sha256']
    result=dict(schema='full111-complete-eight-scope-recovery-custody-v4',originals=rows,wrappers=wrappers,
        files=[dict(copy=archive.name,bytes=archive.stat().st_size,sha256=digest(archive))],
        previous_plan_custody=dict(path=str(previous),sha256=digest(previous),preserved_commit='81d9d655'),
        independent_audit=audit,all_eight_scopes_settled=True,every_original_member_roundtrip_verified=True,
        original_plan_failures_preserved_separately=True,files_deleted=False,compiler_invoked=False,mathematical_acceptance=False)
    (target/'index.json').open('x').write(json.dumps(result,indent=2)+'\n')
    assert shutil.disk_usage(HERE).free>=1536*1024**2
    print(json.dumps(dict(folder=str(target),complete_originals=len(rows),archive_sha256=digest(archive),
        archive_bytes=archive.stat().st_size,remote_disk_available_bytes=audit['disk_available_bytes'])),flush=True)

if __name__=='__main__':main()

