from pathlib import Path
import json,hashlib,re
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 offer=H/'tm2-cobham-transfer-offer-20261012-v4';raw=(offer/'manifest.json').read_bytes();assert sha(raw)=='976E1CE6FF88787E6FFDB4FB11E6D442B7A3A47631BE59BDD377735F3D385341';m=json.loads(raw);data={'manifest.json':raw};deps={}
 for name,row in m['files'].items():
  assert Path(name).name==name;b=(offer/name).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'];b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'))
  if name.endswith('.lean'):assert not re.search(rb'\\u[0-9a-fA-F]{4}|\b(sorry|admit|axiom)\b',b)
  data[name]=b
 root=H/'joint-codec-minimal-source-closure-v3';assert sha((root/'manifest.json').read_bytes())=='5B67D35ED501CC911EDB2CD96994639579A4B7EC57E015790520CB8EA53CB57E';base=json.loads((root/'manifest.json').read_bytes())
 for module in ['OAI.Computability.UniqueGames.Model','OAI.Computability.UniqueGames.Machines.Runtime','Complexitylib.Models.TuringMachine','Complexitylib.Classes.P.Cobham.Internal.Algebra','Complexitylib.Classes.P.Cobham.Vec']:
  row=next(r for r in base['sources'] if r['module']==module);b=(root/row['file']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'];pins=re.findall(r'\b[0-9A-F]{64}\b',m['source_inputs'][module]);assert not pins or pins==[sha(b)];name='dependency.'+module+'.source';data[name]=b;deps[module]=dict(bytes=len(b),sha256=sha(b),actual_source_path=str(root/row['file']),git_blob=row['git_blob'],revision=row['revision'],offered_pin_verified=bool(pins),actual_joint_source_manifest_verified=True)
 d=H/'tm2-cobham-transfer-capture-20261012-v4';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');rows=[]
 for name,b in data.items():(d/name).write_bytes(b);assert (d/name).read_bytes()==b;rows.append(dict(path=name,bytes=len(b),sha256=sha(b)))
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());j=dict(files=rows,manifest_sha256=sha(raw),dependencies=deps,predecessor_index_sha256=sha((H/'tm2-cobham-transfer-capture-20261012-v3/index.json').read_bytes()),local_complexity_TM_snapshot_verified=True,correct_public_Vec_and_internal_Algebra_paths_verified=True,utf8_no_bom_and_literal_unicode_escape_preflight_passed=True,source_only=True,compiler_invoked=False,compiler_admission=False,accepted=False,init_output_and_FP_endpoint_remain_open=True,Full120_scope_changed=False,minimal_joint_four_custom_scope_changed=False,axiom_requests=data['Checks.lean'].count(b'#print axioms '));(d/'index.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(index_sha256=sha((d/'index.json').read_bytes()),files=rows,axiom_requests=j['axiom_requests'])))
if __name__=='__main__':main()
