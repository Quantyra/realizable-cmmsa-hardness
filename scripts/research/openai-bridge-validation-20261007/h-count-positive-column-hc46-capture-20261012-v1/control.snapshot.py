from pathlib import Path
import hashlib,json,re,subprocess
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 offer=H/'h-count-positive-column-hc46-offer-20261012-v1';raw=(offer/'manifest.json').read_bytes();assert sha(raw)=='1694618F4E093EBF8A75F9A7BFBA578C997730ED64C7CAFB68C7D8BD0961A7FF';m=json.loads(raw);data={};dependencies=[];planning=[]
 for r in m['offer_files']:
  p=Path(r['path']);assert p.parent.resolve()==offer.resolve();b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'))
  if p.suffix=='.lean':assert not re.search(rb'\\u[0-9a-fA-F]{4}|\b(sorry|admit|axiom)\b',b)
  data[p.name]=b
 for r in m['dependencies']:
  p=Path(r['path']);b=p.read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];dependencies.append(dict(**r,bytes_verified=True))
 for name,r in m['planning'].items():
  p=Path(r['path']);b=p.read_bytes();row=dict(name=name,offered_sha256=r['sha256'],disk_sha256=sha(b),disk_pin_matches=sha(b)==r['sha256'])
  if 'commit' in r:
   root=Path('C:/Users/dfred/Desktop/Projects/IGH/Quantyra-AI-Planning');b=subprocess.check_output(['git','show',r['commit']+':'+p.relative_to(root).as_posix()],cwd=root);row.update(raw_git_stdout_sha256=sha(b),raw_git_pin_matches=sha(b)==r['sha256'],commit=r['commit'])
  planning.append(row)
 data['manifest.json']=raw;d=H/'h-count-positive-column-hc46-capture-20261012-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');rows=[]
 for name,b in data.items():
  (d/name).write_bytes(b);assert (d/name).read_bytes()==b;rows.append(dict(file=name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,dependency_bytes_verified=dependencies,planning_pins=planning,source_only=True,compiler_invoked=False,accepted=False,compiler_admission=False,unused_hiPos_warning_possible=True,existing_live_full120_scope_changed=False,axiom_requests=data['Checks.lean'].count(b'#print axioms '));(d/'index.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(index=str(d/'index.json'),index_sha256=sha((d/'index.json').read_bytes()),files=rows,dependencies=len(dependencies),planning=planning)))
if __name__=='__main__':main()
