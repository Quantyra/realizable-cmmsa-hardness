"""Qualified full-original gates, separate warning seals and independent VM receipt.
No compiler, source edits or Git mutation. Executed generic audit remains untouched.
"""
import json,re,runpy,sys,subprocess
from collections import Counter
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
m=runpy.run_path(str(HERE/'controller.py'),run_name='finish_full66_import')
runner=m['configure'](); c=m['common']; run=m['PACKAGE']/'runs'/sys.argv[1]
term=json.loads((run/'terminal.json').read_bytes()); assert term['vm_terminal_receipt']['status']=='TERMINATED'
cap=m['PACKAGE']/'captures'/term['capture']; manifest=json.loads((cap/'manifest.json').read_bytes()); d=run/'remote-evidence'
load=lambda p:json.loads(p.read_bytes())
def save(p,v):
 data=c.json_bytes(v)
 if p.exists():assert p.read_bytes()==data,p
 else:c.write_new(p,data)
custody=load(run/'custody.json')
assert custody['before_stop'] and custody['remote_sha256']==custody['repository_sha256']==custody['short_sha256']==c.file_sha(Path(custody['repository_path']))==c.file_sha(Path(custody['short_path']))
expected={n:r['sha256'] for n,r in manifest['project_sources'].items()}; expected.update({n:r['sha256'] for n,r in manifest['configs'].items()})
assert load(d/'source-before.json')==expected==load(d/'source-after.json')
for n,row in manifest['project_sources'].items():assert c.file_sha(cap/'inputs'/n)==row['sha256']
initial=load(cap/'inherited-files-before.json')
assert c.inherited_now()==initial
assert c.inherited_status_now()==load(cap/'inherited-status-before.json')
heads=load(cap/'heads-before.json')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=c.REPO).decode().strip()==heads['head']
assert subprocess.check_output(['git','rev-parse','origin/main'],cwd=c.REPO).decode().strip()==heads['origin_main']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=c.REPO).strip()
save(run/'authorized-successor-preservation.json',{'all_initial_inherited_states_unchanged':True,'inherited_states':len(initial),'all_frozen_compiled_inputs_preserved':True,'frozen_owned_files':len(m['OWNED']),'captured_sources':len(manifest['project_sources']),'authorized_mutable_paths':load(HERE/'authorized-new-author-paths.json')['author_paths'],'original_raw_audit_unchanged':True,'local_compilation':False})
cache=load(d/'verified-cache-provenance.json'); objects=load(d/'object-after.json')
comparison={'cache_objects':len(cache['objects']),'changed':[n for n,h in cache['objects'].items() if objects.get(n)!=h],'compiler_equal':load(d/'compiler-identity.json')==cache['compiler'],'packages_equal':load(d/'package-source-hashes.json')==cache['package_sources'],'core_equal':load(d/'core-source-hashes.json')==cache['core_sources']}
assert comparison['cache_objects']==566 and not comparison['changed'] and all(comparison[n] for n in ['compiler_equal','packages_equal','core_equal'])
save(run/'cache-comparison.json',comparison)
observation=run/'independent-termination-recovery'; observation.mkdir();control=runner.Control(observation)
final=control.describe();assert final['status']=='TERMINATED'
save(observation/'receipt.json',{'utc':c.utc(),'state':final,'independent':True})
baseline=load(HERE/'current-warning-baseline.json'); supplement=load(HERE/'supplemental-inherited-coverage-baseline.json')
assert baseline['original_seal_sha256']==c.file_sha(m['PACKAGE']/'warning-baseline-seal.json')
assert baseline['original_union_headers']==baseline['current_union_headers']==981
prior_baseline=HERE.parent/'retry-69b/current-warning-baseline.json'
assert supplement['original_baseline_sha256']==c.file_sha(prior_baseline)
assert load(prior_baseline)==baseline
assert c.file_sha(HERE/'current-warning-baseline.json')==manifest['files']['harness/retry-70b/current-warning-baseline.json.snapshot']['sha256']
save(run/'warning-baseline-byte-lineage.json',{'current_frozen_baseline_sha256':c.file_sha(HERE/'current-warning-baseline.json'),'prior_pushed_baseline_sha256':c.file_sha(prior_baseline),'complete_parsed_baseline_equality':True,'difference':'CRLF to LF during report directory preparation; no header/source/config/policy content change','original_supplement_pin_retained':True})
assert supplement['header_count']==283 and supplement['native_exit']==0
assert supplement['compiler_identity']==cache['compiler']
for n,row in supplement['source_pins'].items():assert manifest['project_sources'][n]['sha256']==row['sha256']
for n,row in supplement['config_pins'].items():assert manifest['configs'][n]['sha256']==row['sha256']
old=Counter(baseline['baseline_headers']); expanded=Counter(supplement['warning_headers']); assert not (old.keys()&expanded.keys())
both=old|expanded;stages=[];diagnostics=[];texts=[]
for i in range(7):
 text='\n'.join((d/f'stage-{i}.{s}').read_text(encoding='utf-8',errors='replace') for s in ['stdout','stderr']); texts.append(text)
 headers=Counter(re.sub(r'/home/dfredriksen_quantyra_org/cmmsa_[^/]+/','<RUN>/',line) for line in text.splitlines() if re.match(r'^(?:warning\s*:|[^\s].*:\d+:\d+:\s*warning\s*:)',line))
 owned=Counter({h:n for h,n in headers.items() if any(rel in h for rel in m['OWNED'])}); inherited=headers-owned
 rows={'index':i,'exit':int((d/f'stage-{i}.native-exit').read_text()),'warning_headers':sum(headers.values()),'owned_headers':dict(owned),'owned_above_frozen_baseline':dict(owned-old),'retained_original981_headers':dict(headers&old),'retained_supplement283_headers':dict(headers&expanded),'inherited_dependency_headers':dict(inherited),'inherited_above_frozen_baseline':dict(inherited-both),'new_owned_headers':dict({h:n for h,n in owned.items() if any(rel in h for rel in m['OWNED'][-14:])})}
 stages.append(rows);lines=text.splitlines()
 for j,line in enumerate(lines):
  match=re.match(r'^(?:error:\s*)?(.+\.lean):(\d+):(\d+):\s*(?:error:\s*)?(.*)',line)
  if not match or 'warning:' in line or 'error:' not in line:continue
  file,num,col,message=match.groups();relative=next((n for n in manifest['project_sources'] if file.endswith(n)),None)
  end=next((k for k in range(j+1,len(lines)) if re.match(r'^(?:error:|warning:|.+\.lean:\d+:\d+: (?:error|warning):)',lines[k])),len(lines))
  diagnostics.append({'stage':i,'file':file,'line':int(num),'column':int(col),'message':message,'owned':relative in m['OWNED'],'exact_block':'\n'.join(lines[j:end])})
save(run/'warning-classification.json',{'policy':'Separate pre-run981+283 inherited-coverage comparisons, Root06243c5. No historical RED rewrite, suppression or final warning-debt discharge. New owned warnings require zero. Further first-covered inherited headers remain unqualified.','baseline_union_headers':1264,'original981_seal_sha256':c.file_sha(m['PACKAGE']/'warning-baseline-seal.json'),'original981_current_mapping_sha256':c.file_sha(HERE/'current-warning-baseline.json'),'supplement283_sha256':c.file_sha(HERE/'supplemental-inherited-coverage-baseline.json'),'stages':stages})
save(run/'lean-diagnostics.json',diagnostics);c.write_new(run/'lean-diagnostics.txt','\n\n'.join(r['exact_block'] for r in diagnostics))
profiles=c.axiom_profiles(texts[6]); requests=c.REQUESTED_AXIOMS; assert len(requests)==172
bad={n:profiles.get(n) for n in requests if n not in profiles or not set(profiles[n])<=c.STANDARD_AXIOMS}
modules={n.removeprefix('lean/').removesuffix('.lean').replace('/','.'):n for n in manifest['project_sources']};pending=list(m['OWNED']);closure=set()
while pending:
 n=pending.pop()
 if n in closure:continue
 closure.add(n)
 for names in re.findall(r'^\s*import\s+([^\n]+)',(cap/'inputs'/n).read_text(encoding='utf-8'),re.M):pending.extend(modules[x] for x in names.split() if x in modules)
missing=[n for n in sorted(closure) if '.lake/build/lib/lean/'+n.removeprefix('lean/').removesuffix('.lean')+'.olean' not in objects]
pins=load(HERE/'current-axiom-owner-identities.json');assert pins['manifest_sha256']==c.file_sha(cap/'manifest.json')
assert {r['qualified'] for r in pins['requests']}==set(requests)
for row in pins['requests']:assert row['current_capture_sha256']==manifest['project_sources'][row['owner_file']]['sha256']
warn=[r for r in stages if r['owned_above_frozen_baseline'] or r['new_owned_headers'] or r['inherited_above_frozen_baseline']]
green=all(r['exit']==0 for r in stages) and not bad and not missing and not warn
value={'run':run.name,'capture':cap.name,'full_original_A22_HC46_selected_native_gates_green':green,'all_seven_stage_exits':[r['exit'] for r in stages],'original_requested_axioms':172,'axiom_profiles':profiles,'bad_or_missing_axioms':bad,'project_closure_sources':len(closure),'project_closure':sorted(closure),'missing_compiled_objects':missing,'warning_regressions':warn,'cache_objects_unchanged':566,'current_capture_owner_identities':pins['requests'],'independent_vm_status':final['status'],'custody_sha256':custody['remote_sha256'],'accepted':False,'helper_credit':0,'scope':m['common'].CLAIM,'legacy_raw_audit_preserved':True,'local_compilation':False}
save(run/'full-original-a22-hc46-native-gates.json',value)
summary={k:value[k] for k in ['run','capture','full_original_A22_HC46_selected_native_gates_green','all_seven_stage_exits','original_requested_axioms','project_closure_sources','cache_objects_unchanged','custody_sha256','independent_vm_status','accepted','local_compilation']}
summary.update({'owned_error_headers':sum(x['owned'] for x in diagnostics),'owned_warning_headers':[sum(r['owned_headers'].values()) for r in stages],'inherited_regression_headers':[sum(r['inherited_above_frozen_baseline'].values()) for r in stages],'bad_profiles':len(bad),'missing_objects':len(missing)})
save(HERE/'native-report.json',summary);c.write_new(HERE/'native-report.md','# Original A22 / HC46 native result\n\n'+json.dumps(summary,indent=2)+'\n\nRaw generic audit remains unchanged. Native gates do not constitute mathematical acceptance. Full original target reviews remain required; inherited warning debt remains open.\n')
print(json.dumps(summary,indent=2))
