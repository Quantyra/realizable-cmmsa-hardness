from pathlib import Path
import json,hashlib,subprocess
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'local-three-sat-binary-codec-offer-20261012-v2';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='4FE4DEE1EDEBEA5EC41FF1988526B4BBF49EAE2518D1F404D56D41C262C51ADF';m=json.loads(raw);data={}
 for r in m['files']:
  b=(s/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));data[r['path']]=b
 deps=[]
 for r in m['dependencies']:
  name=Path(r['path']).name;p=Path('C:/Users/dfred/.quantyra/reviews')/dict(Encoding='pinned-encoding.tmp',ThreeSAT='pinned-threeSAT.tmp',Syntax='pinned-threeSAT-syntax.tmp')[Path(name).stem];b=p.read_bytes();data['dependency.'+Path(name).stem+'.source']=b;assert sha(b)==r['sha256'];deps.append(dict(path=str(p),bytes=len(b),sha256=sha(b),declared_revision=r['revision'],source_hash_verified=True,git_revision_independently_rechecked=False))
 planning=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning');pins=[]
 for name,c in m['planning_argument_pins'].items():
  commit=subprocess.check_output(['git','rev-parse',c+'^{commit}'],cwd=planning).decode().strip();b=subprocess.check_output(['git','show',commit+':docs/research/pvnp/openai-math-source-bridge-crosswalk-2026-10-06.md'],cwd=planning);pins.append(dict(role=name,commit=commit,raw_crosswalk_sha256=sha(b),raw_bytes=len(b)))
 assert sha((H/'local-three-sat-binary-codec-capture-20261012-v1/index.json').read_bytes())==m['prior_capture']['index_sha256'];assert sha((H/'local-three-sat-binary-codec-capture-20261012-v1/LocalThreeSATBinaryCodec.lean').read_bytes())==m['prior_capture']['source_sha256'];d=H/'local-three-sat-binary-codec-capture-20261012-v2';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');data['manifest.json']=raw;rows=[]
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(original_path=n,copy_path=q.name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),dependencies=deps,planning=pins,encoding_utf8_no_bom=True,axiom_requests=data['Checks.lean'].count(b'#print axioms '),compiler_invoked=False,accepted=False,decoder_normal_form_only=True,scannerMatchesDecoder_proved=False,fp_witness_proved=False,semantic_endpoint_proved=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(capture=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['LocalThreeSATBinaryCodecSemantics.lean']),axiom_requests=j['axiom_requests'])))
if __name__=='__main__':main()
