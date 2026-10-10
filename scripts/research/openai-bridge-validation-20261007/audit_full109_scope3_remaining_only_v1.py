"""Audit interrupted original + independent complete state + remaining-only receipt."""
import hashlib
import json
from pathlib import Path
from full109_builder02_controller import ROOT
from audit_full109_small_cache_recovery_v3_v8 import main as original_audit
from custody_checks import digest

def main():
    original_audit('plan',3)
    here=Path(__file__).parent
    original=ROOT/'cache-repoint-controls/20261010T094620126320Z'
    commands=json.loads((original/'commands.json').read_bytes())
    assert len(commands)==3 and [c['native_exit'] for c in commands]==[0,0,1]
    assert '--execute' in commands[-1]['argv'][-5] or any('--execute' in arg for arg in commands[-1]['argv'])
    assert commands[-1]['timed_out'] is False
    assert digest(original/'executed-repoint-control.py')==digest(here/'full109_storage_cache_repoint_v3.py')
    inspected=ROOT/'openssh-partial-inspections-v2/20261010T102820618094Z'
    state=json.loads((inspected/'inspection.json').read_bytes())
    assert state['all_row_states_verified'] and state['verified_completed_rows']==18781
    assert state['recorded_applied_rows']==18780 and state['remaining_rows']==452
    assert state['row_states']==['completed-symlink']*18781+['remaining-regular']*452
    assert not state['recovery_pids'] and not state['boundary_backups_present']
    folder=ROOT/'scope3-remaining-only-controls-v1/20261010T103230099538Z'
    for control_folder in (inspected,folder):
        records=json.loads((control_folder/'commands.json').read_bytes())
        assert len(records)==2 and all(c['native_exit']==0 for c in records)
        for i,command in enumerate(records):
            assert digest(control_folder/f'{i}.stdout')==command['stdout_sha256']
            assert digest(control_folder/f'{i}.stderr')==command['stderr_sha256']
    records=json.loads((folder/'commands.json').read_bytes())
    import shlex
    remote=shlex.split(records[1]['argv'][-1])
    assert remote[:3]==['python3','-B','-c'] and len(remote)==4
    assert remote[3]==(here/'full109_scope3_remaining_only_v1.py').read_text()
    value=json.loads((folder/'inspection.json').read_bytes())
    receipt=value['receipt']
    data=(json.dumps(receipt,indent=2)+'\n').encode()
    assert hashlib.sha256(data).hexdigest().upper()==value['receipt_sha256']
    receipt_path=folder/'verified-remote-receipt.json'
    if receipt_path.exists():assert receipt_path.read_bytes()==data
    else:receipt_path.open('xb').write(data)
    plans=[]
    for op_path in (ROOT/'cache-repoint-controls').glob('*/operation.json'):
        op=json.loads(op_path.read_bytes())
        if op['remote_control'].endswith('-v3') and op['action']=='plan':plans.append(op)
    assert len(plans)==1 and digest(plans[0]['local_result'])==state['plan_sha256']
    plan=json.loads(Path(plans[0]['local_result']).read_bytes())
    assert receipt['applied']==plan['rows']
    assert state['partial_receipt']['applied']==plan['rows'][:18780]
    assert receipt['independently_verified_preexisting_rows']==18781
    assert receipt['remaining_rows_applied']==452
    assert receipt['original_plan_sha256']==state['plan_sha256']
    assert receipt['original_partial_sha256']==state['partial_sha256']
    for key in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked','original_execute_replayed'):
        assert receipt[key] is False
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    assert receipt['disk_after_bytes']>receipt['disk_before_bytes']
    result=dict(scope=3,rows=19233,original_transport_native_exit=1,
        original_failure_preserved=True,completed_before_continuation=18781,remaining_applied=452,
        receipt_sha256=value['receipt_sha256'],disk_after_bytes=receipt['disk_after_bytes'],
        all_plan_rows_verified=True,compiler_invoked=False,original_execute_replayed=False,accepted=False)
    output=ROOT/'storage-receipt-complete-audit-v3-remaining-only-v1.json'
    encoded=(json.dumps(result,indent=2)+'\n').encode()
    if output.exists():assert output.read_bytes()==encoded
    else:output.open('xb').write(encoded)
    print(json.dumps(result))

if __name__=='__main__':main()
