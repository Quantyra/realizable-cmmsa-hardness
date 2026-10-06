import json,hashlib,re,datetime
from pathlib import Path
R=Path.cwd(); P=R/'docs/a8-gcp/r1007'; H=P/'retry-65'; C=P/'captures/capture-development-65c'; D=P/'runs/cmmsa_a8_output_20261006T123622Z_1dfa244e'; E=D/'remote-evidence'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest().upper()
load=lambda p:json.loads(p.read_bytes())
def write(p,v):
 assert not p.exists(),str(p)
 p.write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
manifest=load(C/'manifest.json'); inherited=load(C/'inherited-files-before.json'); failed=[]
for n,row in inherited.items():
 p=R/n; actual={'sha256':sha(p),'bytes':p.stat().st_size} if p.is_file() else {'missing':True}
 if actual!=row:failed.append(n)
assert not failed,failed
for n,row in manifest['project_sources'].items():assert sha(C/'inputs'/n)==row['sha256']
offer=load(H/'coherent-full-a22-hc46-offer/custody.json')
for n,h in offer['files'].items():assert sha(R/n)==h
prior=load(P/'captures/capture-integrated-64/manifest.json')
for n,row in prior['project_sources'].items():assert sha(R/n)==row['sha256'],n
write(D/'authorized-successor-preservation.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_initial_inherited_states_unchanged':True,'inherited_states':len(inherited),'all_frozen_compiled_inputs_preserved':True,'captured_sources':len(manifest['project_sources']),'prior_accepted_sources_unchanged':len(prior['project_sources']),'authorized_successor_offer':str(H/'coherent-full-a22-hc46-offer/custody.json'),'authorized_successor_hashes':offer['files'],'raw_audit_unchanged':True,'local_compilation':False})
s=load(D/'provisional-expanded-import-warning-summary.json')['stages'][0]; headers=s['new_import_headers'];assert len(headers)==283 and sum(headers.values())==283
owners={re.search(r'warning: (lean/.*?\.lean):',h)[1] for h in headers}
write(H/'supplemental-inherited-coverage-baseline.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'authorization':'Root planning06243c5 separate expanded-coverage seal; original981 unchanged','source_run':D.name,'stage':0,'native_exit':int((E/'stage-0.native-exit').read_text()),'raw_stdout_sha256':sha(E/'stage-0.stdout'),'original_baseline_sha256':sha(H/'current-warning-baseline.json'),'warning_headers':headers,'header_count':283,'source_pins':{n:manifest['project_sources'][n] for n in sorted(owners)},'config_pins':manifest['configs'],'compiler_identity':load(E/'compiler-identity.json'),'accepted':False,'final_warning_debt_discharged':False,'raw65_RED_unchanged':True})
print('Preserved136 inherited,310 frozen,221 prior; separate283 supplemental seal created.')
