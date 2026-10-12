from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'local-three-sat-binary-codec-offer-20261012-v6';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='22E65C6E2179387AD36E6F34E44536891C57BDCF46E145D9CB70E5DAF91B718A';m=json.loads(raw);data={}
 for r in m['files']:
  b=(s/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));data[r['path']]=b
 dep=H/'local-three-sat-binary-codec-capture-20261012-v4';prior=(dep/'index.json').read_bytes();assert sha(prior)=='8085E29B4E674FC9DA604EBAA6EA63BF93DA2C49C39AD9E0383932E7CB4E1BBA'
 for r in json.loads(prior)['files']:
  if r['copy_path'].startswith('dependency.'):
   b=(dep/r['copy_path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];data[r['copy_path']]=b
 plan=H/'joint-codec-environment-source-plan-v1';pm=(plan/'manifest.json').read_bytes();pj=json.loads(pm)
 for r in pj['actual_OAI_source_closure']:
  b=(plan/r['copy']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes']
 data['joint-source-plan.manifest.json']=pm;data['prior-runtime.index.json']=prior;data['manifest.json']=raw
 d=H/'local-three-sat-binary-codec-capture-20261012-v6';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');rows=[]
 for n,b in data.items():
  (d/n).write_bytes(b);assert (d/n).read_bytes()==b;rows.append(dict(original_path=n,copy_path=n,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),prior_dependency_index_sha256=sha(prior),actual_OAI_closure_sha256=sha(pm),actual_OAI_closure_files_verified=len(pj['actual_OAI_source_closure']),local_transitive_closure_recompile_pending=True,compiler_invoked=False,accepted=False,axiom_requests=data['Checks.lean'].count(b'#print axioms '))
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),axiom_requests=j['axiom_requests'])))
if __name__=='__main__':main()
