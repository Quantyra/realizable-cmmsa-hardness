"""Read-only run observation or independent GCP terminal verification."""
from pathlib import Path
import json, subprocess, sys, uuid
from datetime import datetime, timezone
from runner import GCLOUD, FLAGS, VM, DESCRIBE
from common import file_sha

sys.stdout.reconfigure(encoding='utf-8')
p=Path(__file__).resolve().parent
run=p/'runs'/sys.argv[1]
terminal=len(sys.argv)>2 and sys.argv[2]=='terminal'
folder=run/('independent-terminal-' if terminal else 'observation-')
folder=folder.with_name(folder.name+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8])
folder.mkdir()
if terminal:
    args=DESCRIBE
else:
    root='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run.name+'-evidence'
    command="ls -lh "+root+"/stage-*; tail -n 6 "+root+"/stage-0.stdout; for f in "+root+"/stage-*.native-exit; do test ! -f \"$f\" || cat \"$f\"; done; tail -n 60 "+root+"/stage-3.stdout 2>/dev/null; tail -n 8 "+root+"/setup.stderr 2>/dev/null"
    args=['compute','ssh',VM,'--tunnel-through-iap','--command='+command]
argv=[GCLOUD,*args,'--quiet',*FLAGS]
with (folder/'stdout').open('wb') as out, (folder/'stderr').open('wb') as err:
    code=subprocess.run(argv,stdout=out,stderr=err,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0)).returncode
result={'argv':argv,'native_exit':code,'utc':datetime.now(timezone.utc).isoformat(),
        'stdout_sha256':file_sha(folder/'stdout'),'stderr_sha256':file_sha(folder/'stderr')}
if terminal and code==0:
    state=json.loads((folder/'stdout').read_bytes())
    result['independently_verified_status']=state['status']
    result['terminated_verified']=state['name']==VM and state['status']=='TERMINATED'
(folder/'receipt.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps({k:state.get(k) for k in ['name','id','status','lastStopTimestamp']})) if terminal and code==0 else print((folder/'stdout').read_text(encoding='utf-8',errors='replace'))
print(folder.relative_to(p))
sys.exit(code)
