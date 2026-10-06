import json,re,hashlib
from pathlib import Path
R=Path.cwd();P=R/'docs/a8-gcp/r1007';H=P/'retry-65';N=P/'retry-66';N.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_bytes())
rows=[r for r in load(H/'axiom-declaration-owner-map.json')['requests'] if r['basis']=='accepted-frozen64-original85'];assert len(rows)==85
O=H/'coherent-full-a22-hc46-offer';offer=load(O/'custody.json');new=[]
for rel,h in offer['files'].items():
 if not rel.endswith('Checks.lean'):continue
 text=(O/Path(rel).name).read_text(encoding='utf-8');main=rel.replace('Checks.lean','.lean');body=(O/Path(main).name).read_text(encoding='utf-8');namespace=re.search(r'^namespace (\S+)',body,re.M)[1]
 for name in re.findall(r'^#print axioms (\S+)',text,re.M):
  qualified=name if name.startswith('PvNP.') else namespace+'.'+name
  new.append({'original_request':name,'qualified':qualified,'owner_file':main,'basis':'coherent-full-A22-HC46-offer','owner_sha256':offer['files'][main]})
assert len(new)==87,len(new);rows+=new;assert len({r['qualified'] for r in rows})==172
(N/'axiom-declaration-owner-map.json').write_text(json.dumps({'scope':'Original full A22/unchangedHC46ExactContract/actual selected consumer; prior85+87new','requests':rows},indent=2)+'\n',encoding='utf-8')
D=P/'runs/cmmsa_a8_output_20261006T123622Z_1dfa244e'; E=D/'remote-evidence'; text=(E/'stage-3.stdout').read_text(encoding='utf-8')
profiles={n:re.findall(r'\b(?:propext|Classical.choice|Quot.sound|sorryAx)\b',a) for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)}
prior=rows[:85];assert all(r['qualified'] in profiles and set(profiles[r['qualified']])<= {'propext','Classical.choice','Quot.sound'} for r in prior)
v={'run':D.name,'prior85_profiles_standard':True,'profiles':{r['qualified']:profiles[r['qualified']] for r in prior},'stages0through3_native':[int((E/f'stage-{i}.native-exit').read_text()) for i in range(4)],'accepted':False,'new_core_import_blocked':True,'compiled_project_objects':len(load(E/'compiled-project-objects.json'))}
(D/'qualified-prior85-native-evidence.json').write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
print('Full172 owner map exact; prior85 standard; compiled count',v['compiled_project_objects'])
