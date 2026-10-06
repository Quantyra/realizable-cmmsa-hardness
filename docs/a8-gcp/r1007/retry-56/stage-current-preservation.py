"""Stage enumerated current-turn evidence and review inputs only, with byte parity."""
from pathlib import Path
import subprocess,hashlib,json
repo=Path(__file__).resolve().parents[4]; package=repo/'docs/a8-gcp/r1007'
roots=['docs/a8-gcp/r1007/retry-56','docs/a8-gcp/r1007/captures/capture-integrated-56','docs/a8-gcp/r1007/runs/cmmsa_a8_output_20261006T083408Z_44012904','docs/reviews/full-original-a11-a7-20261006T0845Z']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=repo).strip()
attrs=repo/'.gitattributes'; text=attrs.read_text(encoding='utf-8')
for root in roots:
    rule=root+'/** -text'
    if rule not in text:text+='\n'+rule
attrs.write_bytes((text+'\n').encode())
spec=package/'retry-56/current-stage-pathspec.nul'
paths=[p.relative_to(repo).as_posix() for root in roots for p in (repo/root).rglob('*') if p.is_file()]
paths+=['.gitattributes',spec.relative_to(repo).as_posix()]
paths=sorted(set(paths)); spec.write_bytes(b'\0'.join(n.encode() for n in paths)+b'\0')
subprocess.run(['git','add','--pathspec-from-file='+str(spec),'--pathspec-file-nul'],cwd=repo,check=True)
staged=subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=repo).decode().strip('\0').split('\0')
assert set(staged)<=set(paths)
index={x.split('\t',1)[1]:x.split()[1] for x in subprocess.check_output(['git','ls-files','--stage'],cwd=repo).decode().splitlines()}
for name in staged:
    data=(repo/name).read_bytes(); blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert index[name]==blob,name
assert not any(n.startswith('docs/storage-review/') or n.startswith('lean/') for n in staged)
print(json.dumps({'staged_files':len(staged),'exact_byte_parity':True,'inherited_staging':False,'sources_changed':False},indent=2))
