"""Capture exact namespace-only successor bundle; no compiler or acceptance."""
from pathlib import Path
import json,hashlib,subprocess,tarfile
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-decay-namespace-repair-offer-20261011-v1';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='39772A7A41FFC22A977A13CD845F9ED30C15AEDA8E2FA51D217A53754FB07A78';m=json.loads(raw);data={}
 for x in m['files']:
  b=(s/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];b.decode('utf-8');assert not b.startswith(bytes.fromhex('efbbbf'));data[x['path']]=b
 assert sha(Path(m['inspection']['path']).read_bytes())==m['inspection']['sha256']
 for r in m['source_successors']:
  b=data[r['path']];old=Path(r['parent_source']).read_bytes();assert sha(old)==r['parent_source_sha256'];assert sha(Path(r['parent_capture_index']).read_bytes())==r['parent_capture_index_sha256'];assert sha(Path(r['parent_manifest']).read_bytes())==r['parent_manifest_sha256']
  ending=b'\r\n' if b'\r\n' in old else b'\n';addition=('open '+' '.join(r['added_namespaces'])).encode()+ending+ending;assert b.count(addition)==1 and b.replace(addition,b'',1)==old
  assert data[r['checks_path']]==Path(r['checks_parent']).read_bytes();assert sha(data[r['checks_path']])==r['checks_sha256']
 r=m['planning_argument'];b=subprocess.check_output(['git','show',r['committed_head']+':'+r['relative_path']],cwd=r['repository']);assert sha(b)==r['committed_blob_sha256'];section=b.decode().split(r['heading'],1)[1].split('\n## ',1)[0];assert sha((r['heading']+section).encode())==r['section_sha256']
 d=H/'numeric-decay-namespace-repair-capture-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');data['manifest.json']=raw;rows=[]
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.parent.mkdir(exist_ok=True,parents=True);q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(original_path=n,copy_path=q.relative_to(d).as_posix(),bytes=len(b),sha256=sha(b)))
 (d/'inspection.snapshot.json').write_bytes(Path(m['inspection']['path']).read_bytes());(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(original_directory=str(s),files=rows,manifest_sha256=sha(raw),all_five_exact_inverse_byte_checks=True,parent_source_index_manifest_checks_pins_verified=True,planning_committed_blob_and_section_verified=True,compiler_invoked=False,accepted=False,explicit_execution_dependency_rebind_required=True,inherited_global_posterior_source_game_true_rejected=True,source_game_law_identified=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),manifest_sha256=sha(raw))))
if __name__=='__main__':main()
