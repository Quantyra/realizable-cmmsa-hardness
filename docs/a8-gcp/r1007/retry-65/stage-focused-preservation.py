import json,hashlib,subprocess,datetime
from pathlib import Path
R=Path.cwd();P=R/'docs/a8-gcp/r1007';A=P/'retry-65';B=P/'retry-66'
run=lambda args:subprocess.check_output(['git',*args],cwd=R)
assert not run(['diff','--cached','--name-only']).strip()
roots=['docs/a8-gcp/r1007/retry-65','docs/a8-gcp/r1007/retry-66','docs/a8-gcp/r1007/captures/capture-development-65','docs/a8-gcp/r1007/captures/capture-development-65b','docs/a8-gcp/r1007/captures/capture-development-65c','docs/a8-gcp/r1007/runs/cmmsa_a8_output_20261006T123622Z_1dfa244e']
files=set()
for args in [['ls-files','--others','--exclude-standard','-z','--',*roots],['diff','--name-only','-z','--',*roots]]:files.update(n for n in run(args).decode('utf-8').split('\0') if n)
offer=json.loads((A/'coherent-full-a22-hc46-offer/custody.json').read_bytes());files.update(offer['files'])
files={n for n in files if '__pycache__' not in Path(n).parts and not n.endswith('.pyc')}
assert all((R/n).is_file() for n in files)
for n,h in offer['files'].items():assert hashlib.sha256((R/n).read_bytes()).hexdigest().upper()==h
rows={n:{'sha256':hashlib.sha256((R/n).read_bytes()).hexdigest().upper(),'bytes':(R/n).stat().st_size} for n in sorted(files)}
receipt=A/'focused-preservation-stage.json';receipt.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'initial_head':run(['rev-parse','HEAD']).decode().strip(),'scope_roots':roots,'source_ownership':list(offer['files']),'files':rows,'inherited_dirt_excluded':True,'raw_byte_staging':True,'no_local_compilation':True},indent=2)+'\n',encoding='utf-8');files.add(receipt.relative_to(R).as_posix())
for n in sorted(files):
 data=(R/n).read_bytes();blob=run(['hash-object','-w','--no-filters',n]).decode().strip();assert blob==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();subprocess.run(['git','update-index','--add','--cacheinfo','100644,'+blob+','+n],cwd=R,check=True,stdout=subprocess.DEVNULL)
staged=set(run(['diff','--cached','--name-only','-z']).decode().split('\0'))-{''};assert staged==files,(len(staged),len(files))
for n in files:
 data=(R/n).read_bytes();assert run(['rev-parse',':'+n]).decode().strip()==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
print(json.dumps({'staged_files':len(files),'raw_blob_FS_parity':True,'inherited_excluded':True}))
