"""Read-only exact-run process/setup/stage observation."""
import json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
sys.dont_write_bytecode=True
PACKAGE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(PACKAGE))
from runner import GCLOUD,FLAGS,VM
run=sys.argv[1]; folder=PACKAGE/'runs'/run/('process-observation-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')); folder.mkdir()
root='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run+'-evidence'
command="date -u; ps -eo pid,ppid,etimes,stat,args | grep -E '"+run+"|[l]ake build|[/]lean |[c]loud_capture.py'; ls -lh "+root+"; tail -n 8 "+root+"/setup.stderr 2>/dev/null; tail -n 4 "+root+"/stage-0.stdout 2>/dev/null; grep '^error:' "+root+"/stage-1.stdout 2>/dev/null | head -n 12"
argv=[GCLOUD,'compute','ssh',VM,'--tunnel-through-iap','--command='+command,'--quiet',*FLAGS]
r=subprocess.run(argv,capture_output=True,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
(folder/'stdout').write_bytes(r.stdout); (folder/'stderr').write_bytes(r.stderr)
(folder/'receipt.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'argv':argv,'native_exit':r.returncode,'read_only':True},indent=2),encoding='utf-8')
sys.stdout.reconfigure(encoding='utf-8'); print(r.stdout.decode()); print(folder.relative_to(PACKAGE))
