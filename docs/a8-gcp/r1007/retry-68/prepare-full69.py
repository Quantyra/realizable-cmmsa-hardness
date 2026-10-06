import json,hashlib,re,ast,datetime
from pathlib import Path
R=Path.cwd();P=R/'docs/a8-gcp/r1007';A=P/'retry-68';B=P/'retry-69';D=P/'runs/cmmsa_a8_output_20261006T135903Z_115656e2';C=P/'captures/capture-full-a22-hc46-68';E=D/'remote-evidence';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest().upper()
term=json.loads((D/'terminal.json').read_bytes());assert term['vm_terminal_receipt']['status']=='TERMINATED'
qualified=json.loads((A/'native-report.json').read_bytes());assert qualified['independent_vm_status']=='TERMINATED' and qualified['cache_objects_unchanged']==566
assert qualified['all_seven_stage_exits']==[0,0,0,0,1,125,125]
assert all(n==0 for n in qualified['inherited_regression_headers'])
old=json.loads((P/'retry-67/coherent-full-a22-hc46-successor/custody.json').read_bytes())['files'];repair=json.loads((A/'native-68-operator-repair-offer/custody.json').read_bytes())['files'];new=old|repair;O=A/'coherent-full-a22-hc46-successor';O.mkdir();B.mkdir()
for n,h in new.items():
 assert sha(R/n)==h
 (O/Path(n).name).write_bytes((R/n).read_bytes())
(O/'custody.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':new,'previous_capture':C.name,'previous_capture_unchanged':True,'only_source_change_vs68':'Operator09192 exact6error proof/API namespace repair; unchanged statements/options/normalizations','no_local_compilation':True,'accepted':False,'helper_credit':0},indent=2)+'\n',encoding='utf-8')
assert (E/'stage-4.stdout').read_bytes()==(D/'live-owned-20261006T1409080000/native-stdout.snapshot').read_bytes()
owner=json.loads((A/'axiom-declaration-owner-map.json').read_bytes());profiles={n:re.findall(r'\b(?:propext|Classical.choice|Quot.sound|sorryAx)\b',v) for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(E/'stage-3.stdout').read_text(encoding='utf-8'),re.S)};prior=[r for r in owner['requests'] if r['basis']=='accepted-frozen64-original85'];assert len(prior)==85 and all(r['qualified'] in profiles and set(profiles[r['qualified']])<= {'propext','Classical.choice','Quot.sound'} for r in prior)
compiled=len(json.loads((E/'compiled-project-objects.json').read_bytes()))
(D/'qualified-prior85-native-evidence.json').write_text(json.dumps({'run':D.name,'prior85_profiles_standard':True,'profiles':{r['qualified']:profiles[r['qualified']] for r in prior},'stages0through3_native':[int((E/f'stage-{i}.native-exit').read_text()) for i in range(4)],'compiled_project_objects':compiled,'accepted':False,'new_full_scope_RED':True},indent=2)+'\n',encoding='utf-8')
s=(A/'controller.py').read_text(encoding='utf-8').replace('retry-68','retry-69').replace('full68_import','full69_import').replace('capture-full-a22-hc46-68','capture-full-a22-hc46-69').replace("PRIOR='cmmsa_a8_output_20261006T134011Z_55568d8b'","PRIOR='cmmsa_a8_output_20261006T135903Z_115656e2'").replace("CANDIDATE_DIR=PACKAGE/'retry-67/coherent-full-a22-hc46-successor'","CANDIDATE_DIR=PACKAGE/'retry-68/coherent-full-a22-hc46-successor'").replace("priorcap=PACKAGE/'captures/capture-full-a22-hc46-67'","priorcap=PACKAGE/'captures/capture-full-a22-hc46-68'")
s=s.replace('==306','=='+str(compiled)).replace('Run67 successful stages0through3','Run68 successful stages0through3').replace('Run67 identity-pinned stages0through3','Run68 identity-pinned stages0through3');ast.parse(s);(B/'controller.py').write_text(s,encoding='utf-8')
for name in ['current-warning-baseline.json','current-dependency-pins.json','accepted-a9-source.lean.snapshot','supplemental-inherited-coverage-baseline.json','authorized-new-author-paths.json']:(B/name).write_bytes((A/name).read_bytes())
registry=json.loads((B/'authorized-new-author-paths.json').read_bytes());registry['current_full_candidate_hashes']=new;registry['prior_registration']=str(A/'authorized-new-author-paths.json');(B/'authorized-new-author-paths.json').write_text(json.dumps(registry,indent=2)+'\n',encoding='utf-8')
for row in owner['requests']:
 if row['owner_file'] in new:row['owner_sha256']=new[row['owner_file']]
owner['previous_owner_map_sha256']=sha(A/'axiom-declaration-owner-map.json');owner['scope']='Full original A22/unchangedHC46/selected same172requests; only Operator09192 proof/API successor';(B/'axiom-declaration-owner-map.json').write_text(json.dumps(owner,indent=2)+'\n',encoding='utf-8')
for name in ['pin-current-axiom-owners.py','observe-current-stage.py','fetch-full-a22-live.py','finish-native.py']:
 t=(A/name).read_text(encoding='utf-8').replace('capture-full-a22-hc46-68','capture-full-a22-hc46-69');ast.parse(t);(B/name).write_text(t,encoding='utf-8')
report=(A/'author-report.md').read_text(encoding='utf-8').replace('retry-67/coherent-full-a22-hc46-successor/custody.json','retry-68/coherent-full-a22-hc46-successor/custody.json')
for n,h in repair.items():report=report.replace(old[n],h)
(B/'author-report.md').write_text(report,encoding='utf-8')
(A/'settled-full68-closeout.json').write_text(json.dumps({'run':D.name,'native_report':qualified,'custody':json.loads((D/'custody.json').read_bytes()),'independent_TERM':json.loads((D/'independent-termination/receipt.json').read_bytes()),'preservation':json.loads((D/'authorized-successor-preservation.json').read_bytes()),'prior85_standard':True,'final_provisional_stage4_identical':True,'seals981and283_unchanged':True,'current_successor_custody_sha256':sha(O/'custody.json'),'accepted':False,'helper_credit':0,'raw_generic_RED_preserved':True},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'coherent_full_candidate':14,'requests':172,'compiled_prior_inventory':compiled,'same_cache_scope':566,'local_compilation':False}))
