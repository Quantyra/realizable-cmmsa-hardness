"""Complete exact applied-row verification before any dependent recovery/resume."""
import json
import sys
from pathlib import Path
from custody_checks import digest
from prepare_builder02_full102 import OUTPUT


def main(number):
    assert number in (1,2)
    operations={}
    remote='/home/dfredriksen_quantyra_org/full102-storage-cache-repoint-v'+str(number)
    for path in (OUTPUT/'cache-repoint-controls').glob('*/operation.json'):
        op=json.loads(path.read_bytes())
        if op['remote_control']==remote and op['action'] in ('plan','execute'):
            assert op['action'] not in operations
            assert digest(op['local_result'])==op['result_sha256']
            operations[op['action']]=op
    assert set(operations)=={'plan','execute'}
    plan=json.loads(Path(operations['plan']['local_result']).read_bytes())
    receipt=json.loads(Path(operations['execute']['local_result']).read_bytes())
    assert operations['plan']['control_sha256']==operations['execute']['control_sha256']
    assert receipt['applied']==plan['rows'] and len(receipt['applied'])==9672
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for field in ['warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked']:
        assert receipt[field] is False
    assert receipt['disk_after_bytes']>receipt['disk_before_bytes']
    value=dict(schema='full102-complete-execution-receipt-audit-v1',scope=number,
               operation=operations['execute'],plan_sha256=operations['plan']['result_sha256'],rows_exact=9672,
               allocation=sum(r['allocated_bytes'] for r in receipt['applied']),disk_after_bytes=receipt['disk_after_bytes'],
               content_and_reversibility_preserved=True,compiler_invoked=False,accepted=False)
    p=OUTPUT/('recovery-receipt-audit-v'+str(number)+'.json');b=(json.dumps(value,indent=2)+'\n').encode()
    if p.exists():assert p.read_bytes()==b
    else:p.write_bytes(b)
    print(json.dumps(dict(scope=number,rows=9672,disk_after_bytes=receipt['disk_after_bytes'],receipt_sha256=operations['execute']['result_sha256'],audit_sha256=digest(p))))


if __name__=='__main__':main(int(sys.argv[1]))
