from pathlib import Path
import json,hashlib,subprocess,re
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 s=H/'numeric-numbered-occurrence-producer-offer-20261012-v12';raw=(s/'manifest.json').read_bytes();assert sha(raw)=='97517F44FFCBEDF839786EFB06B897DDE9E5E29198DD3E35404B8A56AED4032D';m=json.loads(raw);data={}
 for r in m['files']:
  b=(s/r['path']).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));assert not re.search(rb'\\u[0-9a-fA-F]{4}',b) if r['path'].endswith('.lean') else True;data[r['path']]=b
 for r in m['pinned_imports']:
  p=H/r['path'];p=p if p.exists() else s/r['path'];b=p.read_bytes();assert sha(b)==r['sha256']
  if 'bytes' in r:assert len(b)==r['bytes']
  if 'capture_index_sha256' in r:assert sha((p.parent/'index.json').read_bytes())==r['capture_index_sha256']
 r=m['planning_argument'];b=subprocess.check_output(['git','show',r['committed_head']+':'+r['relative_path']],cwd=r['repository']);whole_pin_matches=sha(b)==r['raw_git_stdout_sha256'];actual_file_sha256=sha(b);blob=subprocess.check_output(['git','rev-parse',r['committed_head']+':'+r['relative_path']],cwd=r['repository']).decode().strip();assert blob==r['committed_blob_sha1'];assert r['section_extraction_rule']=='Raw committed Git bytes from the named heading inclusive through EOF.';section=b[b.index(r['heading'].encode()):];assert sha(section)==r['section_sha256'] and len(section)==r['section_bytes']
 assert data['ActualNumberedOccurrenceProducer.lean']==(H/'numeric-numbered-occurrence-producer-capture-v5/ActualNumberedOccurrenceProducer.lean').read_bytes()
 d=H/'numeric-numbered-occurrence-producer-capture-v12';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');data['manifest.json']=raw;rows=[]
 for n,b in data.items():
  q=d/('offered.gitattributes' if n=='.gitattributes' else n);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);assert q.read_bytes()==b;rows.append(dict(original_path=n,copy_path=q.relative_to(d).as_posix(),bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),dependencies_source_and_indexes_verified=True,planning_section_verified=True,planning_file_pin_verified=whole_pin_matches,planning_whole_file_discrepancy=dict(offered_sha256=r['raw_git_stdout_sha256'],actual_raw_git_sha256=actual_file_sha256),planning_section_convention='raw committed Git bytes heading inclusive through EOF',planning_field_label_discrepancy=dict(field='committed_blob_sha1',actual_identity_kind='Git SHA1 blob object',value=blob,verified=True),encoding_utf8_no_bom=True,axiom_requests=data['Checks.lean'].count(b'#print axioms '),compiler_invoked=False,accepted=False,literal_ascii_unicode_escape_source_defect=False,compiler_admission=False,compiler_admission_requires_actual_producer_access_gap_resolution=True)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(capture=str(d),index_sha256=sha((d/'index.json').read_bytes()),source_sha256=sha(data['ActualNumberedOccurrenceProducer.lean']),axiom_requests=j['axiom_requests'])))
if __name__=='__main__':main()
