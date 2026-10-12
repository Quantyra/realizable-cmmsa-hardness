from pathlib import Path
import json,hashlib,subprocess
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-numbered-occurrence-producer-offer-20261012-v5';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='C496E5FDEF2990590FB6856EE59DF2AEC3BC89A0358C41731BF60F72988D23F3';m=json.loads(raw);data={};entry_discrepancies=[]
 external_pins={'ActualNumberedOccurrenceProducer.lean':'C220E9A6DA2FFC6247DEBE3503C3EE278E20DCFDA30CEE35F4F107629CECCC6F','ARGUMENT.md':'5CF513AC8B82AFB656F7252F15706FAAD741B60DD8F98374BCD7A3ECB2174B07'}
 for r in m['files']:
  b=(s/r['path']).read_bytes();assert sha(b)==external_pins.get(r['path'],r['sha256']);
  if sha(b)!=r['sha256'] or len(b)!=r['bytes']:entry_discrepancies.append(dict(path=r['path'],declared_sha256=r['sha256'],actual_sha256=sha(b),declared_bytes=r['bytes'],actual_bytes=len(b)))
  b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));data[r['path']]=b
 for r in m['pinned_imports']:
  p=H/r['path'];b=p.read_bytes();assert sha(b)==r['sha256']
  if 'bytes' in r:assert len(b)==r['bytes']
  if 'capture_index_sha256' in r:assert sha((p.parent/'index.json').read_bytes())==r['capture_index_sha256']
 r=m['planning_argument'];b=subprocess.check_output(['git','show',r['committed_head']+':'+r['relative_path']],cwd=r['repository']);whole_pin_matches=sha(b)==r['raw_git_stdout_sha256'];actual_file_sha256=sha(b);blob=subprocess.check_output(['git','rev-parse',r['committed_head']+':'+r['relative_path']],cwd=r['repository']).decode().strip();assert blob==r['committed_blob_sha1'];section=(r['heading']+b.decode().split(r['heading'],1)[1].split('\n## ',1)[0]+'\n').encode();assert sha(section)==r['section_sha256'] and len(section)==r['section_bytes']
 d=H/'numeric-numbered-occurrence-producer-capture-v5';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');data['manifest.json']=raw;rows=[]
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(original_path=n,copy_path=q.name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),manifest_entry_discrepancies=entry_discrepancies,externally_offered_hashes_verified=True,internal_manifest_entries_verified=not entry_discrepancies,dependencies_source_and_indexes_verified=True,planning_section_verified=True,planning_file_pin_verified=whole_pin_matches,planning_whole_file_discrepancy=dict(offered_sha256=r['raw_git_stdout_sha256'],actual_raw_git_sha256=actual_file_sha256),planning_section_convention='heading inclusive through byte before next heading, including separator newline',planning_field_label_discrepancy=dict(field='committed_blob_sha1',actual_identity_kind='Git SHA1 blob object',value=blob,verified=True),encoding_utf8_no_bom=True,axiom_requests=data['Checks.lean'].count(b'#print axioms '),compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(capture=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['ActualNumberedOccurrenceProducer.lean']),axiom_requests=j['axiom_requests'])))
if __name__=='__main__':main()
