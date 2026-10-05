"""Selective Git writer, gated on bounded acceptance and independent termination."""
from pathlib import Path
import json, subprocess, sys
from common import REPO, SOURCE, CHECKS, file_sha, inherited_now

p=Path(__file__).resolve().parent
root=p.relative_to(REPO).as_posix()
report=json.loads((p/'report.json').read_bytes())
assert report['bounded_acceptance_green'] and report['independent_terminal_proofs']
assert report['remote_exits']=={'native-exit':0,'aggregate.native-exit':0,'finish.native-exit':0}
raw=subprocess.check_output
flags=getattr(subprocess,'CREATE_NO_WINDOW',0)
def git(*args):
    return raw(['git','-c','core.longpaths=true',*args],cwd=REPO,creationflags=flags)
assert git('branch','--show-current').decode().strip()=='main'
assert not git('diff','--cached','--name-only').strip()
assert git('remote','get-url','origin').decode().strip()=='https://github.com/Quantyra/realizable-cmmsa-hardness.git'
head=git('rev-parse','HEAD').decode().strip()
assert git('ls-remote','origin','refs/heads/main').decode().split()[0]==head
run=p/'runs'/report['run']
capture=json.loads((run/'audit.json').read_bytes())['capture']
before=json.loads((p/'captures'/capture/'inherited-files-before.json').read_bytes())
assert inherited_now()==before
assert file_sha(REPO/SOURCE)==report['source_sha256']
assert file_sha(REPO/CHECKS)==report['checks_sha256']
# Only the two candidate files and this new bounded evidence subtree are staged.
subprocess.run(['git','-c','core.longpaths=true','add','--',SOURCE,CHECKS,root],cwd=REPO,check=True,creationflags=flags)
paths=git('diff','--cached','--name-only','-z').decode().strip('\0').split('\0')
assert SOURCE in paths and CHECKS in paths
assert all(r in {SOURCE,CHECKS} or r.startswith(root+'/') for r in paths)
subprocess.run(['git','-c','core.longpaths=true','diff','--cached','--check','--',SOURCE,CHECKS],cwd=REPO,check=True,creationflags=flags)
import hashlib
for rel,key in [(SOURCE,'source_sha256'),(CHECKS,'checks_sha256')]:
    assert hashlib.sha256(git('show',':'+rel)).hexdigest().upper()==report[key]
result={'parent':head,'staged_paths':paths,'staged_candidate_hashes_match':True,
        'inherited_files_preserved_before_commit':True,'acceptance_run':report['run']}
(p/'git-delivery-preflight.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
subprocess.run(['git','-c','core.longpaths=true','add','--',str((p/'git-delivery-preflight.json').relative_to(REPO))],cwd=REPO,check=True,creationflags=flags)
commit_args=['git','-c','core.longpaths=true','commit','-m','Compile analytic A8 output coordinate transport']
commit_output=subprocess.run(commit_args,cwd=REPO,check=True,capture_output=True,creationflags=flags)
commit=git('rev-parse','HEAD').decode().strip()
assert inherited_now()==before
push_args=['git','-c','core.longpaths=true','push','origin','HEAD:main']
push_output=subprocess.run(push_args,cwd=REPO,check=True,capture_output=True,creationflags=flags)
assert git('ls-remote','origin','refs/heads/main').decode().split()[0]==commit
delivery={'implementation_commit':commit,'push':'origin/main verified',
          'commit_argv':commit_args,'commit_exit':commit_output.returncode,
          'commit_stdout':commit_output.stdout.decode('utf-8',errors='replace'),
          'commit_stderr':commit_output.stderr.decode('utf-8',errors='replace'),
          'push_argv':push_args,'push_exit':push_output.returncode,
          'push_stdout':push_output.stdout.decode('utf-8',errors='replace'),
          'push_stderr':push_output.stderr.decode('utf-8',errors='replace'),
          'unrelated_dirty_files_preserved':True}
(p/'git-delivery-result.json').write_text(json.dumps(delivery,indent=2)+'\n',encoding='utf-8')
report['git_status']={'implementation_commit':commit,'push':'origin/main verified',
                      'receipt_commit':'Follows to preserve delivery receipts; final head reported by owner'}
(p/'report.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
with (p/'report.txt').open('a',encoding='utf-8') as f:
    f.write(f'\nImplementation commit {commit}; pushed and verified on origin/main. Delivery receipt commit follows.\n')
inventory={str(f.relative_to(p)):file_sha(f) for f in p.rglob('*') if f.is_file() and f.name!='evidence-files.sha256.json' and '__pycache__' not in f.parts}
(p/'evidence-files.sha256.json').write_text(json.dumps(inventory,indent=2)+'\n',encoding='utf-8')
receipt_paths=[(p/name).relative_to(REPO).as_posix() for name in ['git-delivery-result.json','report.json','report.txt','evidence-files.sha256.json']]
subprocess.run(['git','-c','core.longpaths=true','add','--',*receipt_paths],cwd=REPO,check=True,creationflags=flags)
assert set(git('diff','--cached','--name-only','-z').decode().strip('\0').split('\0'))==set(receipt_paths)
subprocess.run(['git','-c','core.longpaths=true','commit','-m','Record bounded A8 compiler delivery receipts'],cwd=REPO,check=True,capture_output=True,creationflags=flags)
receipt_commit=git('rev-parse','HEAD').decode().strip()
subprocess.run(push_args,cwd=REPO,check=True,capture_output=True,creationflags=flags)
assert git('ls-remote','origin','refs/heads/main').decode().split()[0]==receipt_commit
assert inherited_now()==before
assert not git('diff','--cached','--name-only').strip()
assert not git('status','--porcelain=v1','--untracked-files=normal','--',SOURCE,CHECKS,root).strip()
print(json.dumps({'implementation_commit':commit,'receipt_commit':receipt_commit,
                  'push':'origin/main verified','unrelated_dirty_files_preserved':True}))
