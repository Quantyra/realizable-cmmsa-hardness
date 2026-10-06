"""Read-only provisional raw profiling streams; no compiler or source edits."""
import json,subprocess,sys,hashlib
from pathlib import Path
from datetime import datetime,timezone
PACKAGE=Path(__file__).resolve().parent.parent
run=sys.argv[1]; stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
folder=PACKAGE/'runs'/run/('live-profile-'+stamp); folder.mkdir(exist_ok=False)
base='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run+'-evidence/stage-4'
rows=[]
for stream in ['stdout','stderr']:
 argv=[r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd','compute','ssh','quantyra-lean-builder-01','--project=quantyra-lean-cert-20260915','--zone=us-central1-a','--account=dfredriksen@quantyra.org','--tunnel-through-iap','--command=cat '+base+'.'+stream]
 r=subprocess.run(argv,capture_output=True,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
 (folder/('native-'+stream+'.snapshot')).write_bytes(r.stdout)
 (folder/(stream+'-transport-stderr')).write_bytes(r.stderr)
 rows.append({'stream':stream,'argv':argv,'native_exit':r.returncode,'bytes':len(r.stdout),'sha256':hashlib.sha256(r.stdout).hexdigest().upper()})
(folder/'receipt.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'streams':rows,'provisional':True,'final_archive_authoritative':True,'compile_started':False},indent=2))
print(json.dumps({'folder':folder.relative_to(PACKAGE).as_posix(),'streams':[{k:v for k,v in x.items() if k!='argv'} for x in rows]},indent=2))
