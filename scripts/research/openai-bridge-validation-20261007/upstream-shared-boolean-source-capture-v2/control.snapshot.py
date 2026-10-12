from pathlib import Path
import json,hashlib,subprocess
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'upstream-shared-boolean-source-offer-20261011-v2';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='B0725DE39F1C9111D04B2D184501867101A57BEEF90900443FB92FBA09B47ABF';m=json.loads(raw);data={}
 for r in m['files']:
  b=(s/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));data[r['path']]=b
 upstream=Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
 for r in m['pinned_upstream_sources']:
  b=(upstream/r['path']).read_bytes();assert sha(b)==r['sha256'];blob=subprocess.check_output(['git','cat-file','blob',m['upstream_revision']+':'+r['path']],cwd=upstream);assert b==blob
 assert sha((H/m['readback']['path']).read_bytes())==m['readback']['sha256']
 assert sha((H/m['captured_source_dependency']['offer']/'UnclonedBinarySource.lean').read_bytes())==m['captured_source_dependency']['sha256']
 assert data['BooleanParityInput.lean']==(H/'shared-boolean-parity-input-capture-v1/BooleanParityInput.lean').read_bytes()
 r=m['planning_argument'];b=subprocess.check_output(['git','show',r['committed_head']+':'+r['relative_path']],cwd=r['repository']);text=b.decode('utf8');heading='## '+r['heading'];section=heading+text.split(heading,1)[1].split('\n## ',1)[0];assert sha(section.encode())==r['section_sha256']
 d=H/'upstream-shared-boolean-source-capture-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');data['manifest.json']=raw;rows=[]
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(original_path=n,copy_path=q.name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),upstream_revision=m['upstream_revision'],baseline_pinned_git_blobs_verified=len(m['pinned_upstream_sources']),planning_section_verified=True,encoding_utf8_no_bom=True,compiler_invoked=False,accepted=False,interop_unaccepted=True)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(capture=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['SharedBooleanSource.lean']))))
if __name__=='__main__':main()
