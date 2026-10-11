"""Exact uncompiled successor custody, preserving offered metadata."""
import hashlib,json
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-original-law-amplification-offer-v3';m=json.loads((s/'manifest.json').read_bytes())
 assert sha((s/'manifest.json').read_bytes())=='1504A6BC86FDDF5F553258C4EB60E27BD247DC5B7B110DCA7F63B77724646CC0'
 for r in m['files'].values():assert sha((s/r['path']).read_bytes())==r['sha256']
 deps=m['frozen_dependencies']+m['active_candidate_dependencies']
 for r in deps:assert sha((H/r['path']).read_bytes())==r['sha256']
 for key in ('parent_capture','h11_predecessor_capture'):
  r=m[key];assert sha((H/r['artifact']/'index.json').read_bytes())==r['index_sha256']
 a=Path('C:/Users/dfred/.quantyra/builder02/full114-exact-real-complex-operators-repair4-resource02/input-archive.tar.gz')
 assert sha(a.read_bytes())==m['source_archive']['sha256']
 d=H/'numeric-original-law-amplification-capture-v3';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 for p in sorted(s.iterdir()):
  assert p.is_file() and not p.is_symlink();b=p.read_bytes();b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
  q=d/('offered.gitattributes' if p.name=='.gitattributes' else p.name);q.write_bytes(b);assert q.read_bytes()==b
  rows.append(dict(path=p.name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 index=dict(original_directory=str(s),files=rows,verified_dependencies=deps,active_h12_capture_index_sha256=sha((H/'numeric-side-extension-formal-capture-v12/index.json').read_bytes()),archive_sha256=m['source_archive']['sha256'],compiler_invoked=False,accepted=False,immutable_capture=True,observations=['Offered capture_ack_pending fields preserved unchanged; H12 independently captured before this capture.'])
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(sha((d/'index.json').read_bytes()))
if __name__=='__main__':main()
