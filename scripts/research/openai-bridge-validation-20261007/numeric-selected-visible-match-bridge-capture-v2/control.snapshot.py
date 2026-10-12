"""Exact frozen offer and diagnostic custody only; no compiler invocation."""
import json,hashlib,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-selected-visible-match-bridge-offer-20261011-v2';raw=(s/'manifest.json').read_bytes();m=json.loads(raw);assert sha(raw)=='D34734D78D3B186904645AD326C639BA5C53566DC5FBD0436E042B9893922610'
 assert sha((s/'ActualSelectedVisibleMatchBridge.lean').read_bytes())=='103EEBCCDFE7E0B327A431D1611B6D2BEC93023CF8C7FFF47AED1EECD98F7741'
 offered=m['files']+m.get('diagnostic_checkpoints',[]);data={}
 for r in offered:
  p=s/r['path'];assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes']
  if not r['path'].startswith('diagnostics/'):
   b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'))
  data[r['path']]=b
 a=Path(m['full114_archive']['path']);assert sha(a.read_bytes())==m['full114_archive']['sha256']
 with tarfile.open(a,'r:gz') as t:
  for r in m['parent_dependencies']:
   b=t.extractfile(r['member']).read();assert sha(b)==r['sha256'] and len(b)==r['bytes']
  b=t.extractfile('lean-toolchain').read();assert sha(b)==m['toolchain']['sha256'] and b.decode().strip()==m['toolchain']['value']
  assert m['mathlib_revision'] in t.extractfile('lake-manifest.json').read().decode()
 for r in m['candidate_dependencies']:
  b=(H/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];assert sha((H/r['capture_index']).read_bytes())==r['capture_sha256']
 old=H/'numeric-selected-visible-match-bridge-capture-v1/ActualSelectedVisibleMatchBridge.lean'
 new=(s/'ActualSelectedVisibleMatchBridge.lean').read_bytes()
 added=b'open ActualOriginalLawFullDecoderIntegration\n'
 assert new.count(added)==1 and new.replace(added,b'',1)==old.read_bytes()
 d=H/'numeric-selected-visible-match-bridge-capture-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 data['manifest.json']=raw
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);assert q.read_bytes()==b
  rows.append(dict(original_path=n,copy_path=q.relative_to(d).as_posix(),sha256=sha(b),bytes=len(b),excluded_from_candidate_source_scope=n.startswith('diagnostics/')))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 j=dict(original_directory=str(s),files=rows,manifest_sha256=sha(raw),dependencies_verified=True,compiler_invoked=False,accepted=False,author_claims_not_adopted=True,namespace_repair_source_only=True,diagnostics_excluded_from_candidate_scope=True)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),manifest_sha256=sha(raw))))
if __name__=='__main__':main()
