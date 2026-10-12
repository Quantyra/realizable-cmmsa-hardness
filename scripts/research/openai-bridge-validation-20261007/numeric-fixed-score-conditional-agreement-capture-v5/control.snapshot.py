"""Lossless V5 custody including quarantined diagnostics; no Lean invocation."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-fixed-score-conditional-agreement-offer-20261011-v5';m=json.loads((s/'manifest.json').read_bytes())
 assert sha((s/'manifest.json').read_bytes())=='DAE42FE45BD10887795D2F82106CB86EB77077BFEE675E722A9B62BB26816A26'
 for r in m['files']+m['diagnostic_artifacts']:
  b=(s/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
 a=Path(m['full114_archive']['path']);assert sha(a.read_bytes())==m['full114_archive']['sha256'];verified=[];nulls=[]
 with tarfile.open(a,'r:gz') as t:
  for r in m['direct_imports']+m['dependency_set']:
   if r['member'].startswith('lean/'):b=t.extractfile(r['member']).read()
   elif r.get('source_record','').startswith('this V5'):b=(s/r['member']).read_bytes()
   else:
    c=H/r['source_record'];b=(c/r['member']).read_bytes()
    assert sha((c/'index.json').read_bytes())==r['capture_index_sha256']
    assert sha((c/'manifest.json').read_bytes())==r['capture_manifest_sha256']
   assert len(b)==r['bytes'] and sha(b)==r['sha256'];verified.append(r)
  for row in m['import_capture_pins']:
   c=H/row['capture'];assert sha((c/'index.json').read_bytes())==row['capture_index_sha256']
   assert sha((c/'manifest.json').read_bytes())==row['capture_manifest_sha256']
   b=(c/row['source_member']).read_bytes();assert len(b)==row['source_bytes'] and sha(b)==row['source_sha256']
   assert row['full114_archive_sha256']==m['full114_archive']['sha256'] and row['mathlib_revision']==m['mathlib_revision']
   for r in row['dependencies']:
    b=t.extractfile(r['member']).read();assert len(b)==r['bytes'] and sha(b)==r['sha256']
   for r in row.get('candidate_dependencies',[]):
    if r is None:nulls.append(row['capture']);continue
    p=Path(r['path']);p=p if p.is_absolute() else H/p;b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
  record=m['source_record']
  for n,key,size in [('lean-toolchain','toolchain_sha256','toolchain_bytes'),('lake-manifest.json','lake_manifest_sha256','lake_manifest_bytes')]:
   b=t.extractfile(n).read();assert sha(b)==record[key] and len(b)==record[size]
  assert m['mathlib_revision'] in t.extractfile('lake-manifest.json').read().decode()
 record=m['source_record'];p=H/record['path']/'source-index.json';assert sha(p.read_bytes())==record['source_index_sha256'] and p.stat().st_size==record['source_index_bytes']
 d=H/'numeric-fixed-score-conditional-agreement-capture-v5';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 for p in sorted(s.rglob('*')):
  if not p.is_file():continue
  assert not p.is_symlink();b=p.read_bytes();rel=p.relative_to(s);diagnostic='diagnostics' in rel.parts
  if not diagnostic:b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
  destination=rel.with_name('offered.gitattributes') if rel.name=='.gitattributes' else rel;q=d/destination;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);assert q.read_bytes()==b
  rows.append(dict(original_path=rel.as_posix(),copy_path=destination.as_posix(),bytes=len(b),sha256=sha(b),excluded_from_candidate_source_scope=diagnostic))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 result=dict(original_directory=str(s),files=rows,verified_dependencies=verified,source_record_index_sha256=record['source_index_sha256'],archive_sha256=m['full114_archive']['sha256'],historical_embedded_null_candidate_metadata_preserved=nulls,diagnostics_quarantined_from_source_scope=True,compiler_invoked=False,accepted=False,immutable_capture=True)
 (d/'index.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(sha((d/'index.json').read_bytes()))
if __name__=='__main__':main()
