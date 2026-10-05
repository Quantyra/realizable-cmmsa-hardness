"""Bounded actual-cache-fault stop: exact current begin child, never a restart."""
import base64,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
run='cmmsa_a8_output_20261005T195325Z_dbc003da'
folder=PACKAGE/'runs'/run/'precompile-stop'; folder.mkdir(exist_ok=False)
script='''from pathlib import Path
import json,os,signal,hashlib
run='cmmsa_a8_output_20261005T195325Z_dbc003da'
evidence=Path('/home/dfredriksen_quantyra_org/cmmsa-evidence')/(run+'-evidence')
assert evidence.is_dir() and not (evidence/'stage-0.stdout').exists(), 'Not precompile; do not interrupt'
matches=[]
for p in Path('/proc').iterdir():
    if not p.name.isdigit(): continue
    try: argv=(p/'cmdline').read_bytes().split(b'\\0')
    except FileNotFoundError: continue
    if len(argv)>=4 and argv[1:4]==[b'cloud_capture.py',b'begin',str(evidence).encode()]:
        stat=(p/'stat').read_text().split(') ',1)[1].split(); parent=int(stat[1])
        parentargv=Path('/proc',str(parent),'cmdline').read_bytes().split(b'\\0')
        assert parentargv[:2]==[b'bash',('/tmp/'+run+'.sh').encode()]
        matches.append({'pid':int(p.name),'argv':[x.decode() for x in argv if x],'ppid':parent,'parent_argv':[x.decode() for x in parentargv if x]})
assert len(matches)==1,matches
artifact=Path('/home/dfredriksen_quantyra_org/cmmsa_a8_output_20261005T191951Z_7ea37ffb/.lake/build/ir/PvNP/RealizableHardness/ActualBinaryMatrixHC46A8AveragedTransport.setup.json')
assert artifact.is_file() and artifact.stat().st_nlink>=2
receipt={'reason':'Actual changed-target setup.json hardlinked from prior cache; preserve old bytes before any target write','artifact':str(artifact),'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest().upper(),'nlink':artifact.stat().st_nlink,'exact_child':matches[0],'target_stages_started':False,'immutable_inputs_changed':False}
(evidence/'precompile-stop.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2),flush=True)
os.kill(matches[0]['pid'],signal.SIGTERM)
'''
encoded=base64.b64encode(script.encode()).decode()
command='python3 -c "import base64;exec(base64.b64decode(\''+encoded+'\'))"'
argv=[r'C:\Users\Dan\AppData\Local\Google\CloudSDKPortable\google-cloud-sdk\bin\gcloud.cmd','compute','ssh','quantyra-lean-builder-01','--project=quantyra-lean-cert-20260915','--zone=us-central1-a','--account=dfredriksen@quantyra.org','--tunnel-through-iap','--command='+command]
result=subprocess.run(argv,capture_output=True,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
(folder/'stdout').write_bytes(result.stdout); (folder/'stderr').write_bytes(result.stderr)
(folder/'receipt.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'argv':argv,'native_exit':result.returncode,'compile':False,'root_authorized_actual_cache_fault_stop':True},indent=2),encoding='utf-8')
print(result.stdout.decode('utf-8','replace')); print(result.stderr.decode('utf-8','replace'))
raise SystemExit(result.returncode)
