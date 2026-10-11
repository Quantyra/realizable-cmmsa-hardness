"""Bind four existing plans and three additional scopes without replaying completed plans."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from full111_builder02_controller import ROOT

HERE=Path(__file__).resolve().parent


def main():
    original=HERE/'full111-settled-cache-recovery-derivation-v2.json'
    additional=HERE/'full111-remaining-cache-helper-derivation-v3.json'
    first=json.loads(original.read_bytes());new=json.loads(additional.read_bytes())
    scopes=first['scopes'][:4]+new['scopes']
    assert [r['number'] for r in scopes]==[111,96,97,98,109,110,'111_small']
    for row in scopes:
        p=HERE/row['helper'];assert digest(p)==row['helper_sha256'];ast.parse(p.read_text(encoding='utf-8'))
    assert new['current_native_run']==first['current_native_run']
    assert new['current_native_terminal_sha256']==first['current_native_terminal_sha256']
    plan_root=ROOT/'settled-cache-recovery-v2/openssh-plan-20261011T044730710232Z'
    for scope in scopes[:4]:
        op=json.loads((plan_root/f"operation-{scope['number']}.json").read_bytes())
        assert op['helper_sha256']==scope['helper_sha256']
        plan_path=Path(op['local_result']);assert digest(plan_path)==op['result_sha256']
        plan=json.loads(plan_path.read_bytes());assert not plan['executed']
        if scope['number']==111:assert all(r['bytes']>=65536 for r in plan['rows'])
    assert scopes[-1]['run']==scopes[0]['run']
    assert '1 <= info.st_size < 65536' in (HERE/scopes[-1]['helper']).read_text()
    value=dict(first);value.update(schema='full111-existing-four-plus-three-disjoint-scopes-v3',scopes=scopes,
        original_derivation_sha256=digest(original),additional_derivation_sha256=digest(additional),
        complete_existing_plans_retained=[111,96,97,98],additional_plan_scopes=[109,110,'111_small'],
        full111_large_small_disjoint_by_logical_size=True,cloud_action_performed=False)
    target=HERE/'full111-settled-cache-recovery-derivation-v3.json';target.open('x').write(json.dumps(value,indent=2)+'\n')
    print(json.dumps(dict(scopes=len(scopes),sha256=digest(target),cloud_action=False)),flush=True)


if __name__=='__main__':main()
