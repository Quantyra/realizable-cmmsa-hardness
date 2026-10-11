"""Preserve capacity inspection; add disjoint remaining scopes to four verified plans."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from full111_builder02_controller import ROOT

HERE=Path(__file__).resolve().parent
ROWS=[]


def derive(parent,target,changes):
    p=HERE/parent;text=p.read_text(encoding='utf-8');records=[]
    for old,new in changes:
        count=text.count(old);assert count>0,(parent,old[:60])
        text=text.replace(old,new);records.append(dict(old=old,new=new,occurrences=count))
    ast.parse(text);q=HERE/target;q.open('xb').write(text.encode())
    ROWS.append(dict(parent=parent,parent_sha256=digest(p),target=target,sha256=digest(q),replacements=records))


def main():
    observation=ROOT/'remaining-capacity-inspections-v1/20261011T045214028242Z'
    value=json.loads((observation/'inspection.json').read_bytes())
    assert [r['number'] for r in value['scopes']]==[109,110,111]
    for row in value['scopes']:
        assert row['small_allocated_bytes']>=384*1024**2
        if row['number']!=111:assert row['small_allocated_bytes']+row['large_allocated_bytes']>=896*1024**2
    assert value['read_only'] and value['content_identity_not_yet_verified']
    for row in json.loads((observation/'transport/commands.json').read_bytes()):
        assert row['native_exit']==0
        for stream in ('stdout','stderr'):assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
    target=HERE/'full111-remaining-capacity-observation-v1';target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    records=[]
    for i,p in enumerate(sorted(p for p in observation.rglob('*') if p.is_file())):
        q=target/(f'{i:03d}-'+p.name);q.open('xb').write(p.read_bytes());assert digest(q)==digest(p)
        records.append(dict(original=str(p),copy=q.name,bytes=p.stat().st_size,sha256=digest(p)))
    (target/'index.json').open('x').write(json.dumps(dict(files=records,original_handle=5537,original_exit=0,
        observation=value,allocated_capacity_is_not_verified_identical_content=True,compiler_invoked=False),indent=2)+'\n')
    parent=(HERE/'derive_full111_settled_cache_recovery_v2.py').read_text(encoding='utf-8')
    derive('derive_full111_settled_cache_recovery_v2.py','derive_full111_remaining_cache_helpers_v3.py',[
        ('for number in (111, 96, 97, 98, 99, 100, 101):',"for number in (109, 110, '111_small'):"),
        ('resource = ROOT if number == 111 else',"resource = ROOT if number == '111_small' else"),
        ("'-v2'","'-v3'"),("'_v2.py'","'_v3.py'"),
        ('        target = HERE /',"        if number == '111_small':\n            replace('info.st_size >= 1', '1 <= info.st_size < 65536')\n            replace('TARGET = 896 * 1024**2', 'TARGET = 384 * 1024**2')\n        target = HERE /"),
        ('target_bytes=5 * 1024**3 if number == 111 else 896 * 1024**2',"target_bytes=384 * 1024**2 if number == '111_small' else 896 * 1024**2"),
        ('full111-settled-cache-recovery-controls-v2','full111-remaining-cache-helper-controls-v3'),
        ('full111-settled-cache-recovery-derivation-v2.json','full111-remaining-cache-helper-derivation-v3.json')])
    # The small 111 scope is strictly below 64KiB and cannot overlap the existing large plan.
    derive('run_full111_settled_cache_openssh_v3.py','run_full111_settled_cache_openssh_v4.py',[
        ('NUMBERS = [111,96,97,98,99,100,101]',"NUMBERS = [111,96,97,98,109,110,'111_small']"),
        ('full111-settled-cache-recovery-derivation-v2.json','full111-settled-cache-recovery-derivation-v3.json'),
        ("    assert [r['number'] for r in scopes] == NUMBERS", "    assert [r['number'] for r in scopes] == NUMBERS\n    partial = json.loads((HERE/'full111-four-plans-scope99-failure-record-v1/index.json').read_bytes())\n    assert partial['original_exit'] == 1 and partial['no_cache_execution_invoked']\n    for row in partial['files']: assert digest(HERE/'full111-four-plans-scope99-failure-record-v1'/row['copy']) == row['sha256']\n    if action == 'plan': scopes = scopes[4:]"),
        ('full111-recovery-plans-openssh-record-v3','full111-recovery-plans-openssh-record-v4')])
    derive('audit_full111_settled_cache_recovery_v2.py','audit_full111_settled_cache_recovery_v3.py',[
        ('run_full111_settled_cache_openssh_v3','run_full111_settled_cache_openssh_v4'),
        ('full111-settled-cache-recovery-derivation-v2.json','full111-settled-cache-recovery-derivation-v3.json'),
        ('complete-audit-v2','complete-audit-v3'),('full111-seven-scope-recovery-audit-v2','full111-seven-scope-recovery-audit-v3')])
    derive('stage_full112_after_recovery_openssh_v2.py','stage_full112_after_recovery_openssh_v3.py',[
        ('audit_full111_settled_cache_recovery_v2','audit_full111_settled_cache_recovery_v3')])
    derive('run_full112_resume_step_v5.py','run_full112_resume_step_v6.py',[
        ("'run_full112_native_openssh_v1.py'}", "'run_full112_native_openssh_v1.py', 'derive_full111_remaining_cache_helpers_v3.py', 'run_full111_settled_cache_openssh_v4.py', 'audit_full111_settled_cache_recovery_v3.py', 'stage_full112_after_recovery_openssh_v3.py', 'preserve_full111_complete_recovery_plans_v4.py'}")])
    (HERE/'full112-capacity-bound-recovery-derivation-v3.json').open('x').write(json.dumps(dict(
        rows=ROWS,observation_index_sha256=digest(target/'index.json'),preserved_existing_plan_scopes=[111,96,97,98],
        new_scopes=[109,110,'111_small'],new_targets_MiB=[896,896,384],
        full111_small_filter='1 <= logical size < 65536; prior Full111 large plan requires >=65536',
        compiler_invoked=False,cloud_action=False,minimum_remote_GiB=40,minimum_local_MiB=1536),indent=2)+'\n')
    print(json.dumps(dict(derived=len(ROWS),cloud_action=False)),flush=True)


if __name__=='__main__':main()
