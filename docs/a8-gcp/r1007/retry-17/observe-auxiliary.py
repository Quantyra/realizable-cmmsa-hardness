"""Read-only predecessor-cache artifact enumeration; no source mutation."""
import base64,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run=sys.argv[1]; folder=PACKAGE/'runs'/run/'auxiliary-cache-preflight'; folder.mkdir(exist_ok=False)
script='''from pathlib import Path
import json
root=Path('/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261005T191951Z_7ea37ffb/.lake/build')
names=['AveragedTransport','AveragedAssembly','EnergyNaturality','PairAssembly','AmbientAssembly','Endpoint']
rows=[]
for p in root.rglob('*'):
    if p.is_file() and any(p.name.startswith('ActualBinaryMatrixHC46A8'+n+s+'.') for n in names for s in ['', 'Checks']):
        rows.append({'path':str(p),'nlink':p.stat().st_nlink,'bytes':p.stat().st_size})
print(json.dumps({'root_exists':root.exists(),'owned_cached_artifacts':rows},indent=2))
'''
encoded=base64.b64encode(script.encode()).decode()
command='python3 -c "import base64;exec(base64.b64decode(\''+encoded+'\'))"'
argv=[r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd','compute','ssh','quantyra-lean-builder-01','--project=quantyra-lean-cert-20260915','--zone=us-central1-a','--account=dfredriksen@quantyra.org','--tunnel-through-iap','--command='+command]
result=subprocess.run(argv,capture_output=True,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
(folder/'stdout').write_bytes(result.stdout); (folder/'stderr').write_bytes(result.stderr)
(folder/'receipt.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'argv':argv,'native_exit':result.returncode,'compile':False},indent=2),encoding='utf-8')
print(result.stdout.decode('utf-8','replace')); print(result.stderr.decode('utf-8','replace'))
raise SystemExit(result.returncode)
