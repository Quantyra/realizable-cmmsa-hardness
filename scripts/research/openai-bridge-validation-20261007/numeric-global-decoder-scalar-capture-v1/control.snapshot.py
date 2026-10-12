"""Exact capture only; no Lean, cloud operation or acceptance."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def cap(folder,target,pin,notes):
 s=H/folder;m=json.loads((s/'manifest.json').read_bytes());assert sha((s/'manifest.json').read_bytes())==pin
 rows=[];content={}
 for p in sorted(s.iterdir()):
  assert p.is_file() and not p.is_symlink(); b=p.read_bytes(); b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
  content[p.name]=b;rows.append(dict(path=p.name,bytes=len(b),sha256=sha(b)))
 if 'offered_files_sha256' in m:
  for n,v in m['offered_files_sha256'].items(): assert sha(content['offered.gitattributes' if n=='.gitattributes' else n])==v
 else:
  for r in m['files']:assert sha(content[r['path']])==r['sha256'] and len(content[r['path']])==r['bytes']
 a=m.get('input_archive',m.get('full114_archive',m.get('full117_input')));ap=Path(a['path']);assert sha(ap.read_bytes())==a['sha256']
 verified=[]
 with tarfile.open(ap,'r:gz') as t:
  pins=m.get('source_dependency_closure_sha256',{})
  for n,v in pins.items():
   b=t.extractfile(n).read();assert sha(b)==v.upper();verified.append(dict(member=n,sha256=v,bytes=len(b)))
  for r in m.get('dependencies',[]):
   b=t.extractfile(r['member']).read();assert sha(b)==r['sha256'] and len(b)==r['bytes'];verified.append(r)
  if 'toolchain' in m:
   if 'lean_toolchain_sha256' in m['toolchain']:
    for n,key in [('lean-toolchain','lean_toolchain_sha256'),('lake-manifest.json','lake_manifest_sha256')]:assert sha(t.extractfile(n).read())==m['toolchain'][key]
   else:
    tc=m['toolchain'];b=t.extractfile(tc.get('member','lean-toolchain')).read();assert sha(b)==tc['sha256'];assert b.decode().strip()==tc['value']
    assert m['mathlib_revision'] in t.extractfile('lake-manifest.json').read().decode()
 for r in m.get('candidate_dependencies',[]):
  rp=Path(r['path']);rp=rp if rp.is_absolute() else H/rp;b=rp.read_bytes();assert sha(b)==r['sha256'] and ('bytes' not in r or len(b)==r['bytes'])
 d=H/target;d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n')
 for n,b in content.items():
  name='offered.gitattributes' if n=='.gitattributes' else n;(d/name).write_bytes(b);assert (d/name).read_bytes()==b
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 index=dict(original_directory=str(s),files=rows,independently_verified_archive_members=verified,observations=notes,compiler_invoked=False,native_verified=False,accepted=False,immutable_capture=True)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(target,sha((d/'index.json').read_bytes()),flush=True)
