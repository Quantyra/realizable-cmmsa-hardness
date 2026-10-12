"""Capture only frozen offered geometry; preserve other available bytes as history."""
import hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-visible-ambient-ladder-offer-20261011-v1';m=json.loads((s/'manifest.json').read_bytes())
 assert sha((s/'manifest.json').read_bytes())=='EC58E54CCA46CC111851CB416FEA11DFF7F4826D579A324E7824DF462BA390C0'
 a=Path(m['input_archive']['path']);assert sha(a.read_bytes())==m['input_archive']['sha256']
 with tarfile.open(a,'r:gz') as t:
  for r in m['dependencies']:
   b=t.extractfile(r['member']).read();assert len(b)==r['bytes'] and sha(b)==r['sha256']
  assert sha(t.extractfile('lean-toolchain').read())==m['toolchain_pins']['lean_toolchain_sha256']
  lake=t.extractfile('lake-manifest.json').read();assert sha(lake)==m['toolchain_pins']['lake_manifest_sha256'] and m['mathlib_revision'] in lake.decode()
 routes={'ActualFunctionalAssignmentAcceptance':'numeric-functional-assignment-acceptance-capture-v1','ActualRestrictedVisiblePair':'numeric-restricted-visible-pair-capture-v2','ActualVisibleLeafAgreementLoss':'numeric-actual-visible-leaf-loss-capture-v1'}
 for r in m['direct_imports']:
  name=r['module'].rsplit('.',1)[-1];c=H/routes[name]
  assert sha((c/(name+'.lean')).read_bytes())==r['sha256'] and sha((c/'index.json').read_bytes())==r['capture_index_sha256']
 for r in m['dependency_manifests']:
  assert sha((H/r['artifact']/'manifest.json').read_bytes())==r['manifest_sha256']
 d=H/'numeric-visible-ambient-ladder-capture-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 offered=set(m['offered_files'])|{'manifest.json'}
 for name in sorted(offered):
  p=s/name;assert p.is_file() and not p.is_symlink();b=p.read_bytes();b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
  if name in m['offered_files']:r=m['offered_files'][name];assert len(b)==r['bytes'] and sha(b)==r['sha256']
  copy='offered.gitattributes' if name=='.gitattributes' else name;(d/copy).write_bytes(b);rows.append(dict(original=name,copy=copy,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 result=dict(files=rows,module_destination=m['module_destination'],only_named_offered_files_are_candidate_sources=True,input_archive_sha256=m['input_archive']['sha256'],exact_direct_capture_routes=routes,dependencies_verified=True,original_first_scratch_and_full_encoding_failure_diagnostic_unavailable=True,reconstruction_not_lossless_recovery=True,compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
 history=H/'numeric-visible-ambient-ladder-history-record-v1';history.mkdir(exist_ok=False);(history/'.gitattributes').write_bytes(b'* -text\n');historical=[]
 for p in sorted(s.rglob('*')):
  if not p.is_file() or p.relative_to(s).as_posix() in offered:continue
  assert not p.is_symlink();rel=p.relative_to(s);q=history/rel;q.parent.mkdir(parents=True,exist_ok=True);b=p.read_bytes();q.write_bytes(b);historical.append(dict(original=str(p),copy=rel.as_posix(),bytes=len(b),sha256=sha(b),offered=False,candidate_input=False))
 (history/'index.json').write_text(json.dumps(dict(files=historical,available_historical_bytes_only=True,original_scratch_bytes_not_claimed=True,excluded_from_candidate_source_scope=True,accepted=False),indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(capture_index_sha256=sha((d/'index.json').read_bytes()),history_index_sha256=sha((history/'index.json').read_bytes()))))
if __name__=='__main__':main()
