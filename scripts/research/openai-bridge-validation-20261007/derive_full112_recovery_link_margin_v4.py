"""Add a disjoint large-object tail to cover the allocation cost of replacement links."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from full111_builder02_controller import ROOT

HERE=Path(__file__).resolve().parent


def main():
    previous=HERE/'full111-settled-cache-recovery-derivation-v3.json'
    assert digest(previous)=='C97B1311D04E840AE19BAA2AFE3E9CE5A9D895B83BAC8A2422791CF960077133'
    derivation=json.loads(previous.read_bytes());large=derivation['scopes'][0]
    source=HERE/large['helper'];assert digest(source)==large['helper_sha256']
    parent_plan=ROOT/'settled-cache-recovery-v2/openssh-plan-20261011T044730710232Z/transport/004.stdout'
    plan_sha='93767BDDEF4365598F0697C3672C9708532233750FA6EB19014BC6BB7657573A'
    assert digest(parent_plan)==plan_sha
    plan=json.loads(parent_plan.read_bytes());assert len(plan['rows'])==9649 and all(r['bytes']>=65536 for r in plan['rows'])
    records=[]
    def derive(parent,target,changes):
        p=HERE/parent;text=p.read_text(encoding='utf-8');applied=[]
        for old,new in changes:
            count=text.count(old);assert count>0,(parent,old)
            text=text.replace(old,new);applied.append(dict(old=old,new=new,occurrences=count))
        ast.parse(text);q=HERE/target;q.open('xb').write(text.encode())
        records.append(dict(parent=parent,parent_sha256=digest(p),target=target,sha256=digest(q),replacements=applied))
    guard="def plan():\n    old, canonical = guards()\n"
    extra=guard+"    excluded_plan = HOME / 'full111-settled-cache-native111-v2/plan.json'\n    assert digest(excluded_plan) == '"+plan_sha+"'\n    excluded_rows = json.loads(excluded_plan.read_bytes())['rows']\n    assert len(excluded_rows) == 9649 and all(row['bytes'] >= 65536 for row in excluded_rows)\n    excluded = {row['relative'] for row in excluded_rows}\n"
    helper='full111_settled_cache_native111_tail_v4.py'
    derive(source.name,helper,[('full111-settled-cache-native111-v2','full111-settled-cache-native111_tail-v4'),
        ('TARGET = 5 * 1024**3','TARGET = 384 * 1024**2'),(guard,extra),
        ('        rel = path.relative_to(old)','        rel = path.relative_to(old)\n        if rel.as_posix() in excluded:\n            continue')])
    tail=dict(large);tail.update(number='111_tail',helper=helper,helper_sha256=digest(HERE/helper),
        source=source.name,source_sha256=digest(source),remote_control='/home/dfredriksen_quantyra_org/full111-settled-cache-native111_tail-v4',
        target_bytes=384*1024**2,excluded_existing_large_plan_sha256=plan_sha,excluded_existing_large_rows=9649,
        logical_size_filter='>=65536; excludes every already planned large row; disjoint from <65536 small scope',
        exact_replacements=records[0]['replacements'])
    result=dict(derivation);result.update(schema='full111-eight-disjoint-recovery-scopes-v4',scopes=derivation['scopes']+[tail],
        parent_derivation_sha256=digest(previous),additional_tail_for_replacement_symlink_allocation_margin=True)
    manifest=HERE/'full111-settled-cache-recovery-derivation-v4.json';manifest.open('x').write(json.dumps(result,indent=2)+'\n')
    derive('run_full111_settled_cache_openssh_v4.py','run_full111_settled_cache_openssh_v5.py',[
        ("NUMBERS = [111,96,97,98,109,110,'111_small']","NUMBERS = [111,96,97,98,109,110,'111_small','111_tail']"),
        ('full111-settled-cache-recovery-derivation-v3.json','full111-settled-cache-recovery-derivation-v4.json'),
        ("if action == 'plan': scopes = scopes[4:]","if action == 'plan': scopes = scopes[7:]"),
        ('full111-recovery-plans-openssh-record-v4','full111-recovery-plans-openssh-record-v5'),
        ('all_seven_plans_verified','all_eight_plans_verified')])
    derive('audit_full111_settled_cache_recovery_v3.py','audit_full111_settled_cache_recovery_v4.py',[
        ('run_full111_settled_cache_openssh_v4','run_full111_settled_cache_openssh_v5'),
        ('full111-settled-cache-recovery-derivation-v3.json','full111-settled-cache-recovery-derivation-v4.json'),
        ('complete-audit-v3','complete-audit-v4'),('seven-scope','eight-scope')])
    derive('stage_full112_after_recovery_openssh_v3.py','stage_full112_after_recovery_openssh_v4.py',[
        ('audit_full111_settled_cache_recovery_v3','audit_full111_settled_cache_recovery_v4'),
        ('all_seven_recovery_scopes_verified','all_eight_recovery_scopes_verified'),('seven-scope','eight-scope')])
    derive('run_full112_resume_step_v6.py','run_full112_resume_step_v7.py',[
        ("'preserve_full111_complete_recovery_plans_v4.py'}", "'preserve_full111_complete_recovery_plans_v4.py', 'run_full111_settled_cache_openssh_v5.py', 'audit_full111_settled_cache_recovery_v4.py', 'stage_full112_after_recovery_openssh_v4.py', 'preserve_full111_complete_recovery_plans_v5.py'}")])
    (HERE/'full112-recovery-link-margin-derivation-v4.json').open('x').write(json.dumps(dict(records=records,
        manifest_sha256=digest(manifest),disjoint_from_existing_large_and_small_plans=True,
        justification='Allocated duplicate bytes are not net recovered bytes; replacement links consume allocation.',
        minimum_remote_GiB=40,minimum_local_MiB=1536,compiler_invoked=False,cloud_action=False),indent=2)+'\n')
    print(json.dumps(dict(total_scopes=8,extra_plan_target_MiB=384,cloud_action=False)),flush=True)


if __name__=='__main__':main()
