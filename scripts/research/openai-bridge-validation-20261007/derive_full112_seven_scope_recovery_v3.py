"""Preserve failed 8GiB planning; derive 5GiB plus six small scopes, unchanged gates."""
import ast
import json
from pathlib import Path
import shutil
import subprocess
from custody_checks import digest
from full111_builder02_controller import ROOT
from full112_builder02_controller import ROOT as NEXT

HERE = Path(__file__).resolve().parent
ROWS=[]


def derive(parent,target,replacements):
    p=HERE/parent; raw=p.read_bytes()
    assert raw==subprocess.check_output(['git','show','eca22c39:scripts/research/openai-bridge-validation-20261007/'+parent],cwd=HERE)
    text=raw.decode('utf-8'); changes=[]
    for old,new in replacements:
        count=text.count(old); assert count>0,(parent,old[:80])
        text=text.replace(old,new); changes.append(dict(old=old,new=new,occurrences=count))
    ast.parse(text); q=HERE/target; q.open('xb').write(text.encode())
    ROWS.append(dict(parent=parent,parent_sha256=digest(p),target=target,sha256=digest(q),replacements=changes))


def main():
    target=HERE/'full111-recovery-eight-gib-plan-failure-v1'
    rows=json.loads((target/'index.json').read_bytes())['files']
    for row in rows: assert digest(target/row['copy'])==row['sha256']
    ROWS.append(dict(already_derived='derive_full111_settled_cache_recovery_v2.py',sha256='A25900062FD3C405E132A57E9FA3890649508133B449BE3BE3463B48EB4107BA', original_derivation='derive_full112_seven_scope_recovery_v2.py', original_derivation_sha256='30D2583071960497A4BA3EF4CBBAD6A4371EDEDEB35FFE2DC5C8AA839E7DB4B4'))
    parent=(HERE/'run_full111_settled_cache_openssh_v2.py').read_text(encoding='utf-8')
    start=parent.index('                if number == 111:')
    end=parent.index('\n            preamble +=',start)+1
    old=parent[start:end]
    fresh=old[old.index('                    preamble += "root.mkdir'):].replace('                    preamble','                preamble')
    derive('run_full111_settled_cache_openssh_v2.py','run_full111_settled_cache_openssh_v3.py',[
        ("RECOVERY = ROOT/'settled-cache-recovery-v1'","RECOVERY = ROOT/'settled-cache-recovery-v2'"),
        ('NUMBERS = [111,96,97,98]','NUMBERS = [111,96,97,98,99,100,101]'),
        ("commands = json.loads((RECOVERY/'20261011T043228243781Z/commands.json').read_bytes())","commands = json.loads((ROOT/'settled-cache-recovery-v1/20261011T043228243781Z/commands.json').read_bytes())"),
        ('full111-settled-cache-recovery-derivation-v1.json','full111-settled-cache-recovery-derivation-v2.json'),
        ("    folder = RECOVERY/", "    prior_failure = json.loads((HERE/'full111-recovery-eight-gib-plan-failure-v1/index.json').read_bytes())\n    assert prior_failure['native_exit'] == 1 and prior_failure['no_cache_execution_invoked']\n    for row in prior_failure['files']: assert digest(HERE/'full111-recovery-eight-gib-plan-failure-v1'/row['copy']) == row['sha256']\n    RECOVERY.mkdir(parents=True, exist_ok=True)\n    folder = RECOVERY/"),
        ('full111-recovery-plans-openssh-record-v2','full111-recovery-plans-openssh-record-v3'),
        ('all_four_plans_verified','all_seven_plans_verified'),(old,fresh),
        ('original planner did not invoke plan; first invocation via OpenSSH','separate seven-scope plan; first invocation for new v2 helpers')])
    derive('compress_full112_committed_custody_v2.py','compress_full112_committed_text_v3.py',[
        ("head.startswith('4930801c')","head.startswith('eca22c39')"),
        ("path.suffix != '.json' or path.stat().st_size <= 250_000", "path.suffix not in ('.stdout', '.stderr', '.txt', '.patch', '.lean', '.md', '') or path.stat().st_size <= 128_000"),
        ('full112-committed-custody-lossless-v2','full112-committed-text-lossless-v3')])
    derive('run_full112_resume_step_v3.py','run_full112_resume_step_v4.py',[
        ("'run_full111_settled_cache_openssh_v2.py'}", "'run_full111_settled_cache_openssh_v2.py', 'run_full111_settled_cache_openssh_v3.py', 'derive_full111_settled_cache_recovery_v2.py'}")])
    (HERE/'full112-seven-scope-recovery-derivation-v3.json').open('x').write(json.dumps(dict(
        rows=ROWS,failed_plan_preservation_sha256=digest(target/'index.json'),
        new_scopes=[111,96,97,98,99,100,101],large_target_GiB=5,small_target_MiB=896,
        remote_reserve_GiB=40,local_reserve_MiB=1536,compiler_invoked=False,cloud_action=False),indent=2)+'\n')
    print(json.dumps(dict(preserved_failed_originals=len(rows),new_controls=len(ROWS),cloud_action=False)),flush=True)


if __name__=='__main__':main()
