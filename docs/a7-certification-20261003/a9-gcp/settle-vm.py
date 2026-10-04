"""Observe an already requested GCP stop; never invoke a compiler."""
from pathlib import Path
import subprocess,json,time
out=Path(__file__).resolve().parent
g=r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd'
rows=[]
for i in range(30):
    args=[g,'compute','instances','describe','quantyra-lean-builder-01',
        '--project=quantyra-lean-cert-20260915','--zone=us-central1-a','--format=value(status)']
    p=subprocess.run(args,capture_output=True,timeout=90,creationflags=subprocess.CREATE_NO_WINDOW)
    rows.append({'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        'args':args,'exit':p.returncode,'stdout':p.stdout.decode(errors='replace'),
        'stderr':p.stderr.decode(errors='replace')})
    (out/'first-stop-observations.json').write_text(json.dumps(rows,indent=2))
    print(rows[-1]['stdout'].strip(),flush=True)
    if p.returncode==0 and p.stdout.strip()==b'TERMINATED': break
    time.sleep(20)
else: raise RuntimeError('VM did not settle; do not restart a compiler')
