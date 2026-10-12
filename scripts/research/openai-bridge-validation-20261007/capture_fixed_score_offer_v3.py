"""Verify complete frozen author metadata and preserve exact source bytes."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-fixed-score-conditional-agreement-offer-20261011-v3';m=json.loads((s/'manifest.json').read_bytes());assert sha((s/'manifest.json').read_bytes())=='2450AC2EBFF793EF5558419870475BAA21B133E6AE1C61D3629543CDDB762715'
 for r in m['files']:b=(s/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
 a=Path(m['full114_archive']['path']);assert sha(a.read_bytes())==m['full114_archive']['sha256'];verified=[]
 with tarfile.open(a,'r:gz') as t:
  for r in m['direct_imports']+m['dependency_set']:
   if r['member'].startswith('lean/'):
    b=t.extractfile(r['member']).read()
   else:b=(H/'numeric-row-deletion-capture-v1'/r['member']).read_bytes()
   assert len(b)==r['bytes'] and sha(b)==r['sha256'];verified.append(r)
  record=m['source_record']
  for n,key,size in [('lean-toolchain','toolchain_sha256','toolchain_bytes'),('lake-manifest.json','lake_manifest_sha256','lake_manifest_bytes')]:
   b=t.extractfile(n).read();assert sha(b)==record[key] and len(b)==record[size]
  assert m['mathlib_revision'] in t.extractfile('lake-manifest.json').read().decode()
 record=m['source_record'];index=H/record['path']/'source-index.json';assert sha(index.read_bytes())==record['source_index_sha256'] and index.stat().st_size==record['source_index_bytes']
 d=H/'numeric-fixed-score-conditional-agreement-capture-v3';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 for p in sorted(s.iterdir()):
  assert p.is_file() and not p.is_symlink();b=p.read_bytes();b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'));q=d/p.name;q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(path=p.name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 result=dict(original_directory=str(s),files=rows,verified_dependencies=verified,source_record_index_sha256=record['source_index_sha256'],archive_sha256=m['full114_archive']['sha256'],original_partial_capture_index_sha256=sha((H/'numeric-fixed-score-conditional-agreement-capture-v1/index.json').read_bytes()),compiler_invoked=False,accepted=False,immutable_capture=True)
 (d/'index.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(sha((d/'index.json').read_bytes()))
if __name__=='__main__':main()
