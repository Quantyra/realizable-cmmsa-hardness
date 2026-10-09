"""Review every proposed duplicate row against the prior verified canonical scope."""
import json
from pathlib import Path
from custody_checks import digest
from prepare_builder02_full102 import OUTPUT

HERE=Path(__file__).parent


def main():
    prior=OUTPUT.parent/'full100-matrix-fourier-bullet-repair-resource02/consumption-v2/cache-repoint-controls'
    refs=[]
    for p in prior.glob('*/operation.json'):
        op=json.loads(p.read_bytes())
        if op['action']=='plan' and op['remote_control'].endswith('full100-trace-cache-repoint-v5'):
            assert digest(op['local_result'])==op['result_sha256']
            refs.append(op)
    assert len(refs)==1
    old=json.loads(Path(refs[0]['local_result']).read_bytes())
    index={r['relative']:r for r in old['rows']}
    assert len(index)==len(old['rows'])==9672
    records=[]
    for i,run in [(1,'cmmsa_a8_output_20261009T164439Z_83c3fbf9'),(2,'cmmsa_a8_output_20261009T092534Z_c0fd3e11')]:
        matches=[]
        for p in (OUTPUT/'cache-repoint-controls').glob('*/operation.json'):
            op=json.loads(p.read_bytes())
            if op['action']=='plan' and op['remote_control'].endswith('full102-storage-cache-repoint-v'+str(i)):
                matches.append(op)
        assert len(matches)==1
        op=matches[0];p=Path(op['local_result']);assert digest(p)==op['result_sha256']
        value=json.loads(p.read_bytes())
        assert value['old_root']=='/home/dfredriksen_quantyra_org/'+run+'/.lake/packages'
        assert value['canonical_root']==old['canonical_root']
        assert not value['executed'] and not value['compiler_invoked']
        assert value['hash_or_size_mismatches_skipped']==0
        seen=set();allocation=0
        for row in value['rows']:
            rel=Path(row['relative'])
            assert not rel.is_absolute() and '..' not in rel.parts
            assert {'.lake','build','lib','lean'}<=set(rel.parts)
            assert rel.name.endswith(('.olean','.olean.private','.olean.server','.ilean'))
            assert row['relative'] not in seen;seen.add(row['relative'])
            assert row==index[row['relative']], 'Each exact hash/size/allocation row must match the prior reviewed scope'
            allocation+=row['allocated_bytes']
        assert seen==set(index) and allocation==value['allocated_bytes']>=5*1024**3
        records.append(dict(scope=i,run=run,plan_path=str(p),plan_sha256=digest(p),rows=len(seen),
                            all_rows_prior_exact_matches=True,allocation=allocation))
    result=dict(schema='full102-complete-two-plan-row-review-v1',plans=records,
                prior_plan_path=refs[0]['local_result'],prior_plan_sha256=refs[0]['result_sha256'],
                full102_workspace_and_canonical_bytes_excluded_from_mutation=True,
                capture_time_exhaustive_cache_hash_claimed=False,executed=False,accepted=False)
    out=OUTPUT/'storage-plan-complete-review-v1.json';b=(json.dumps(result,indent=2)+'\n').encode()
    if out.exists():assert out.read_bytes()==b
    else:out.write_bytes(b)
    (HERE/'full102-storage-plan-complete-review-v1.json').write_bytes(b)
    print(json.dumps(dict(plans=2,rows_each=9672,total_bytes=sum(r['allocation'] for r in records),review_sha256=digest(out))))


if __name__=='__main__':main()
