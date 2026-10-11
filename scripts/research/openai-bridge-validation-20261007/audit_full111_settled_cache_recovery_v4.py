"""Reconcile complete eight-scope receipts/journals using trusted OpenSSH."""
from datetime import datetime,timezone
import json
from pathlib import Path
import shlex
from custody_checks import digest
from full111_builder02_controller import ROOT,context,local_gates
from run_full111_settled_cache_recovery_v1 import settled
from full112_dedicated_openssh_v1 import Session
from run_full111_settled_cache_openssh_v5 import RECOVERY,NUMBERS

HERE=Path(__file__).resolve().parent
AUDIT=RECOVERY/'complete-audit-v4'


def unique_operation(number,action):
    rows=[]
    for p in RECOVERY.glob('*/operation-*.json'):
        r=json.loads(p.read_bytes())
        if r['number']==number and r['action']==action:
            assert digest(Path(r['local_result']))==r['result_sha256'];rows.append((p,r))
    assert len(rows)==1,(number,action,len(rows))
    return rows[0]


def validate_local_audit():
    report=json.loads((AUDIT/'audit.json').read_bytes())
    assert report['numbers']==NUMBERS and report['all_rows_match']
    assert report['disk_available_bytes']>=40*1024**3
    assert not report['compiler_invoked'] and not report['power_operation']
    for r in report['files']:
        p=Path(r['path']);assert digest(p)==r['sha256'] and p.stat().st_size==r['bytes']
    for n in NUMBERS:
        unique_operation(n,'plan');unique_operation(n,'execute')
    return report


def main():
    settled();loaded,_=context();local_gates(loaded['common'],loaded)
    scopes=json.loads((HERE/'full111-settled-cache-recovery-derivation-v4.json').read_bytes())['scopes']
    assert [s['number'] for s in scopes]==NUMBERS
    files=[];summaries=[]
    def register(path):
        p=Path(path);files.append(dict(path=str(p),bytes=p.stat().st_size,sha256=digest(p)))
    for p in (Path(__file__).resolve(),HERE/'full111-settled-cache-recovery-derivation-v4.json',
              ROOT/'settled-cache-recovery-v1/boot-once.json',ROOT/'settled-cache-recovery-v1/boot-result.json'):
        register(p)
    for scope in scopes:
        pp,pr=unique_operation(scope['number'],'plan');ep,er=unique_operation(scope['number'],'execute')
        plan=json.loads(Path(pr['local_result']).read_bytes());receipt=json.loads(Path(er['local_result']).read_bytes())
        assert receipt['applied']==plan['rows'] and plan['rows']
        assert len({r['relative'] for r in plan['rows']})==len(plan['rows'])
        assert plan['original_archive_sha256']==scope['archive_sha256']
        assert sum(r['allocated_bytes'] for r in plan['rows'])==plan['allocated_bytes']>=scope['target_bytes']
        assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
        assert receipt['disk_after_bytes']>receipt['disk_before_bytes']
        assert not any(receipt[k] for k in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'))
        assert pr['helper_sha256']==er['helper_sha256']==scope['helper_sha256']==digest(HERE/scope['helper'])
        for p in (pp,ep,pr['local_result'],er['local_result'],HERE/scope['helper']):register(p)
        summaries.append(dict(number=scope['number'],rows=len(plan['rows']),allocated_bytes=plan['allocated_bytes'],
            plan_sha256=pr['result_sha256'],receipt_sha256=er['result_sha256']))
    AUDIT.mkdir(exist_ok=False)
    with Session(AUDIT/'transport') as session:
        for scope,summary in zip(scopes,summaries):
            guest="import hashlib,importlib.util,json\nfrom pathlib import Path\nroot=Path("+repr(scope['remote_control'])+")\nhelper=root/"+repr(scope['helper'])+"\nassert hashlib.sha256(helper.read_bytes()).hexdigest().upper()=="+repr(scope['helper_sha256'])+"\nspec=importlib.util.spec_from_file_location('guard',helper)\nmodule=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.guards()\nprint(json.dumps({n:hashlib.sha256((root/n).read_bytes()).hexdigest().upper() for n in ('execution-journal.jsonl','execute-once.json')}))\n"
            metadata=json.loads(session.python(guest).read_bytes())
            decoded={}
            for name in ('execution-journal.jsonl','execute-once.json'):
                p=session.ssh('cat '+shlex.quote(scope['remote_control']+'/'+name))
                assert digest(p)==metadata[name];register(p);decoded[name]=p.read_bytes()
            _,pr=unique_operation(scope['number'],'plan');plan=json.loads(Path(pr['local_result']).read_bytes())
            journal=[json.loads(line) for line in decoded['execution-journal.jsonl'].splitlines()]
            marker=json.loads(decoded['execute-once.json'])
            assert journal==plan['rows']
            assert marker['plan_sha256']==summary['plan_sha256'] and not marker['compiler_invoked']
            summary['journal_rows']=len(journal)
        final=json.loads(session.python("import json,shutil\nprint(json.dumps(dict(disk_available_bytes=shutil.disk_usage('/home/dfredriksen_quantyra_org').free)))\n").read_bytes())
        state=session.state
    assert final['disk_available_bytes']>=40*1024**3
    for p in AUDIT.rglob('*'):
        if p.is_file() and not any(r['path']==str(p) for r in files):register(p)
    local_gates(loaded['common'],loaded)
    report=dict(schema='full111-eight-scope-recovery-audit-v3',utc=datetime.now(timezone.utc).isoformat(),numbers=NUMBERS,
        scopes=summaries,files=files,all_rows_match=True,disk_available_bytes=final['disk_available_bytes'],state=state,
        original_archive_source_terminal_and_quiescence_guards_passed=True,
        compiler_invoked=False,power_operation=False,mathematical_acceptance=False)
    (AUDIT/'audit.json').open('x').write(json.dumps(report,indent=2)+'\n')
    validate_local_audit();print(json.dumps(dict(audit=str(AUDIT/'audit.json'),rows=sum(s['rows'] for s in summaries),disk_available_bytes=report['disk_available_bytes'])),flush=True)


if __name__=='__main__':main()
