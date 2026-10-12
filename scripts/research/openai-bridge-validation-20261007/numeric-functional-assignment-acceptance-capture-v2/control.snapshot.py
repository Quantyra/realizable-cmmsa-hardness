"""Independent immutable source custody; no compiler or cloud operation."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-functional-assignment-acceptance-offer-20261011-v2'
 raw=(s/'manifest.json').read_bytes()
 assert sha(raw)=='41498AE7D3761F8EAAD6726ECD584EB45A65E4E8D0630EAE8B0AFC3E2AABA8E5'
 m=json.loads(raw);files=[];data={}
 for p in [s/n for n in sorted(set(m['offered_files']) | {'manifest.json'})]:
  assert p.is_file() and not p.is_symlink()
  b=p.read_bytes();b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
  data[p.name]=b;files.append(dict(path=p.name,bytes=len(b),sha256=sha(b)))
 for n,r in m['offered_files'].items():assert sha(data[n])==r['sha256'] and len(data[n])==r['bytes']
 a=Path(m['input_archive']['path']);h=hashlib.sha256()
 with a.open('rb') as f:
  for block in iter(lambda:f.read(65536),b''):h.update(block)
 assert h.hexdigest().upper()==m['input_archive']['sha256']
 with tarfile.open(a,'r:gz') as t:
  tool=t.extractfile('lean-toolchain').read();lake=t.extractfile('lake-manifest.json').read()
  assert tool.decode().strip()==m['toolchain']
  assert m['mathlib_revision'] in lake.decode()
  toolpins=dict(lean_toolchain_sha256=sha(tool),lake_manifest_sha256=sha(lake))
 deps=[]
 for r in m['direct_imports']+m['transitive_candidate_imports']:
  routing={'ActualTaggedRowDeletion':'numeric-row-deletion-capture-v1','ActualTaggedCommonLeafCoherence':'numeric-tagged-common-leaf-capture-v2'}
  offered=r.get('offer');folder=H/(offered if offered is not None else routing[r['module'].rsplit('.',1)[-1]])
  matches=[p for p in folder.glob('*.lean') if sha(p.read_bytes())==r['sha256']]
  assert len(matches)==1,(r['module'],str(folder))
  pin=r.get('capture_index_sha256')
  if pin:
   found=[p for p in H.glob('*/index.json') if sha(p.read_bytes())==pin]
   assert len(found)==1
  deps.append(dict(module=r['module'],path=str(matches[0]),sha256=r['sha256'],capture_index_sha256=pin,accepted=False))
 d=H/'numeric-functional-assignment-acceptance-capture-v2';d.mkdir(exist_ok=False)
 (d/'.gitattributes').write_bytes(b'* -text\n')
 for n,b in data.items():
  p=d/('offered.gitattributes' if n=='.gitattributes' else n);p.write_bytes(b);assert p.read_bytes()==b
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 index=dict(original_directory=str(s),files=files,input_archive_sha256=m['input_archive']['sha256'],toolchain_pins=toolpins,verified_candidate_dependencies=deps,observations=['Only named offered files plus manifest retained exactly; unrelated history excluded from candidate scope.','Two offered transitive folder fields are null; capture-owned routing to exact immutable row-deletion/common-leaf captures is verified and offered metadata remains unchanged. V1 immutable; this disjoint successor retains the offered arity-repair observation. Functional interface source only; no acceptance.'],compiler_invoked=False,accepted=False,immutable_capture=True)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(dict(capture=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['ActualFunctionalAssignmentAcceptance.lean']))))
if __name__=='__main__':main()
