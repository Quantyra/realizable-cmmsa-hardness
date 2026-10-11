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
 a=m.get('input_archive',m.get('full114_archive'));ap=Path(a['path']);assert sha(ap.read_bytes())==a['sha256']
 verified=[]
 with tarfile.open(ap,'r:gz') as t:
  pins=m.get('source_dependency_closure_sha256',{})
  for n,v in pins.items():
   b=t.extractfile(n).read();assert sha(b)==v.upper();verified.append(dict(member=n,sha256=v,bytes=len(b)))
  for r in m.get('dependencies',[]):
   b=t.extractfile(r['member']).read();assert sha(b)==r['sha256'] and len(b)==r['bytes'];verified.append(r)
  if 'toolchain' in m:
   for n,key in [('lean-toolchain','lean_toolchain_sha256'),('lake-manifest.json','lake_manifest_sha256')]:assert sha(t.extractfile(n).read())==m['toolchain'][key]
 for r in m.get('candidate_dependencies',[]):
  b=Path(r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes']
 d=H/target;d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n')
 for n,b in content.items():
  name='offered.gitattributes' if n=='.gitattributes' else n;(d/name).write_bytes(b);assert (d/name).read_bytes()==b
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 index=dict(original_directory=str(s),files=rows,independently_verified_archive_members=verified,observations=notes,compiler_invoked=False,native_verified=False,accepted=False,immutable_capture=True)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(target,sha((d/'index.json').read_bytes()),flush=True)
if __name__=='__main__':
 parent=H/'numeric-side-extension-formal-capture-v9/index.json';actual=sha(parent.read_bytes());assert actual=='180F21CF36DC529DD800BEBFCE2DC84A47A6B2E9D6EE0A19BD770CF97BF5AFFC'
 cap('numeric-side-extension-formal-offer-20261011-v10','numeric-side-extension-formal-capture-v10','4298A5B02422B78519E8D9F928FEF1297975B1C5B4192AED961E17F5BC7E2FE4',{'offered_parent_pin_malformed_preserved':True,'actual_h9_index_sha256':actual,'uncompiled':True})
 cap('numeric-varying-completion-exception-offer-20261011-v2','numeric-varying-completion-exception-capture-v2','F4783640AA933C6F18A641E2E62B17DE8BCAC78A8676B9CB434E5899521B7AD8',{'first_offered_source_sha256':'EE5B3685D00472B0501FA5C03BA199BB26050320B624AFF9FD312FF3AA28F1B2','pre_ack_author_mutation_disclosed':True,'no_initial_custody_by_this_controller':True,'original_manifest_overwritten_unavailable':True,'separate_author_reconstruction_pending_capture':True})
