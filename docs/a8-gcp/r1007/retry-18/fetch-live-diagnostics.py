"""Retain exact provisional native stdout; never execute a compiler."""
import json,subprocess,sys,hashlib,re
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run=sys.argv[1]; stage=int(sys.argv[2]); stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
folder=PACKAGE/'runs'/run/('live-stage-'+str(stage)+'-'+stamp); folder.mkdir(exist_ok=False)
base='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run+'-evidence/stage-'+str(stage)
argv=[r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd','compute','ssh','quantyra-lean-builder-01','--project=quantyra-lean-cert-20260915','--zone=us-central1-a','--account=dfredriksen@quantyra.org','--tunnel-through-iap','--command=cat '+base+'.stdout']
r=subprocess.run(argv,capture_output=True,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
(folder/'native-stdout.snapshot').write_bytes(r.stdout); (folder/'transport-stderr').write_bytes(r.stderr)
(folder/'receipt.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'argv':argv,'native_exit':r.returncode,'stdout_sha256':hashlib.sha256(r.stdout).hexdigest().upper(),'provisional_live_snapshot':True,'final_cloud_archive_remains_authoritative':True,'compile_started':False},indent=2),encoding='utf-8')
text=r.stdout.decode('utf-8','strict'); headers=[line for line in text.splitlines() if line.startswith('error: lean/')]
print(folder.relative_to(PACKAGE)); print('\n'.join(headers))
raise SystemExit(r.returncode)
