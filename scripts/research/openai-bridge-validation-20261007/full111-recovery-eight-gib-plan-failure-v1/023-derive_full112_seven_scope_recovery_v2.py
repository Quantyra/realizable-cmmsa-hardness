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
    wrapper=NEXT/'research-resume-20261011/20261011T044120647696Z-acfb856a09e8'
    failed=ROOT/'settled-cache-recovery-v1/openssh-plan-20261011T044205892717Z'
    command=json.loads((wrapper/'command.json').read_bytes()); assert command['native_exit']==1
    for stream in ('stdout','stderr'): assert digest(wrapper/stream)==command[stream+'_sha256']
    commands=json.loads((failed/'transport/commands.json').read_bytes())
    assert [r['native_exit'] for r in commands]==[0,0,1,0]
    for row in commands:
        for stream in ('stdout','stderr'): assert digest(Path(row[stream+'_path']))==row[stream+'_sha256']
    assert 'Insufficient identical dependency-object copies; no changes made' in (failed/'transport/002.stderr').read_text()
    assert not list(failed.glob('operation-*.json'))
    paths=[p for root in (wrapper,failed) for p in root.rglob('*') if p.is_file()]
    paths += [Path(__file__).resolve()]
    assert shutil.disk_usage(HERE).free-sum(p.stat().st_size for p in paths)>=1536*1024**2
    target=HERE/'full111-recovery-eight-gib-plan-failure-v1'; target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows=[]
    for i,p in enumerate(sorted(paths)):
        q=target/(f'{i:03d}-'+p.name);q.open('xb').write(p.read_bytes());assert digest(q)==digest(p)
        rows.append(dict(original=str(p),copy=q.name,bytes=p.stat().st_size,sha256=digest(p)))
    (target/'index.json').open('x').write(json.dumps(dict(files=rows,original_handle=30697,native_exit=1,
        helper_plan_native_exit=1,no_cache_execution_invoked=True,other_scopes_not_attempted=[96,97,98],
        last_progress_record=json.loads((failed/'transport/002.stdout').read_text().splitlines()[-1]),
        last_progress_is_not_total_candidate_count=True,reason='8GiB target exceeds verified eligible large objects',
        compiler_invoked=False,original_failure_unchanged=True),indent=2)+'\n')
    derive('derive_full111_settled_cache_recovery_v1.py','derive_full111_settled_cache_recovery_v2.py',[
        ('four settled runs','seven settled runs'),('(111, 96, 97, 98)','(111, 96, 97, 98, 99, 100, 101)'),
        ("'-v1'","'-v2'"),("'_v1.py'","'_v2.py'"),
        ("        if number == 111:\n            replace('TARGET = 5 * 1024**3', 'TARGET = 8 * 1024**3')\n",''),
        ('target_bytes=8 * 1024**3','target_bytes=5 * 1024**3'),
        ('full111-settled-cache-recovery-controls-v1','full111-settled-cache-recovery-controls-v2'),
        ('full111-settled-cache-recovery-derivation-v1.json','full111-settled-cache-recovery-derivation-v2.json')])
    parent=(HERE/'run_full111_settled_cache_openssh_v2.py').read_text(encoding='utf-8')
    start=parent.index('                if number == 111:')
    end=parent.index('            preamble +=',start)
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
    (HERE/'full112-seven-scope-recovery-derivation-v2.json').open('x').write(json.dumps(dict(
        rows=ROWS,failed_plan_preservation_sha256=digest(target/'index.json'),
        new_scopes=[111,96,97,98,99,100,101],large_target_GiB=5,small_target_MiB=896,
        remote_reserve_GiB=40,local_reserve_MiB=1536,compiler_invoked=False,cloud_action=False),indent=2)+'\n')
    print(json.dumps(dict(preserved_failed_originals=len(rows),new_controls=len(ROWS),cloud_action=False)),flush=True)


if __name__=='__main__':main()
