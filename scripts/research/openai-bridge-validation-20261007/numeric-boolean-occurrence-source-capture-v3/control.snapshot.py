from pathlib import Path
import json,hashlib,subprocess
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-boolean-occurrence-source-offer-20261012-v3';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='C50973669ED4764276C8AD869433DCC27E456DD61C1290C70E320084FB9F6630';m=json.loads(raw);data={}
 for r in m['files']:
  b=(s/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));data[r['path']]=b
 for r in m['candidate_dependencies']:
  b=Path(r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];assert sha(Path(r['capture_index']).read_bytes())==r['capture_sha256']
 assert sha(Path(m['upstream_semantic_readback']['path']).read_bytes())==m['upstream_semantic_readback']['sha256']
 r=m['planning_argument'];b=subprocess.check_output(['git','show',r['committed_head']+':'+r['relative_path']],cwd=r['repository']);section=r['heading']+b.decode().split(r['heading'],1)[1].split('\n## ',1)[0];assert sha(section.encode())==r['section_sha256'] and section.encode()+b'\n'==data['ARGUMENT.md'] and sha(b)==r['committed_blob_sha256']
 assert data['ActualBooleanOccurrenceSource.lean']==(H/'numeric-boolean-occurrence-source-capture-v2/ActualBooleanOccurrenceSource.lean').read_bytes() and data['Checks.lean']==(H/'numeric-boolean-occurrence-source-capture-v2/Checks.lean').read_bytes()
 mismatch=dict(offered_whole_blob_sha256=r['committed_blob_sha256'],actual_raw_git_blob_sha256=sha(b),whole_blob_pin_verified=sha(b)==r['committed_blob_sha256'],section_verified=True)
 d=H/'numeric-boolean-occurrence-source-capture-v3';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');data['manifest.json']=raw;rows=[]
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(original_path=n,copy_path=q.name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),planning_custody_discrepancy=mismatch,dependencies_source_and_index_verified=True,encoding_utf8_no_bom=True,compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(capture=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['ActualBooleanOccurrenceSource.lean']),planning=mismatch)))
if __name__=='__main__':main()
