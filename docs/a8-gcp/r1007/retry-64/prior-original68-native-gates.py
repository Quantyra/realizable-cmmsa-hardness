"""Evaluate complete original A8 gates; never infer mathematical acceptance."""
import json, re, runpy, sys
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='a8_full_gate_import'); m['configure']()
c=m['common']; run=m['PACKAGE']/'runs'/sys.argv[1]
cap=m['PACKAGE']/'captures/capture-integrated-64'
manifest=json.loads((cap/'manifest.json').read_bytes())
d=run/'remote-evidence'
expected={n:r['sha256'] for n,r in manifest['project_sources'].items()}
expected.update({n:r['sha256'] for n,r in manifest['configs'].items()})
assert json.loads((d/'source-before.json').read_bytes())==expected==json.loads((d/'source-after.json').read_bytes())
cache=json.loads((run/'cache-comparison.json').read_bytes())
assert cache['cache_objects']==400 and not cache['changed'] and all(cache[n] for n in ['compiler_equal','packages_equal','core_equal'])
preserved=json.loads((run/'authorized-successor-preservation.json').read_bytes())
assert preserved['all_initial_inherited_states_unchanged'] and preserved['all_frozen_compiled_inputs_preserved']
term=json.loads((run/'independent-termination/receipt.json').read_bytes())
assert term['state']['status']=='TERMINATED'
custody=json.loads((run/'custody.json').read_bytes())
assert custody['before_stop'] and custody['remote_sha256']==custody['repository_sha256']==custody['short_sha256']
assert c.file_sha(Path(custody['repository_path']))==custody['remote_sha256']
modules={n.removeprefix('lean/').removesuffix('.lean').replace('/','.'):n for n in manifest['project_sources']}
pending=list(m['PRIOR_OWNED']); closure=set()
while pending:
    name=pending.pop()
    if name in closure: continue
    closure.add(name)
    text=(cap/'inputs'/name).read_text(encoding='utf-8')
    for imported in re.findall(r'^\s*import\s+([^\n]+)',text,re.M):
        for module in imported.split():
            if module in modules: pending.append(modules[module])
assert any('A11WeightedAggregate' in n for n in closure)
compiled=json.loads((d/'compiled-project-objects.json').read_bytes())
objects=json.loads((d/'object-after.json').read_bytes())
missing=[]
for n in sorted(closure):
    stem='.lake/build/lib/lean/'+n.removeprefix('lean/').removesuffix('.lean')+'.olean'
    if stem not in objects: missing.append(stem)
rows=json.loads((run/'warning-classification.json').read_bytes())['stages'][:4]
requests=[row['qualified'] for row in m['owner_map_rows']() if row.get('basis')=='accepted-frozen59-original68']
assert len(requests)==68
owner_pins=json.loads((here/'current-axiom-owner-identities.json').read_bytes())
assert owner_pins['manifest_sha256']==c.file_sha(cap/'manifest.json')
current_owners={r['qualified']:r for r in owner_pins['requests'] if r['qualified'] in requests}
assert set(current_owners)==set(requests)
for row in current_owners.values():
    assert row['current_capture_sha256']==manifest['project_sources'][row['owner_file']]['sha256']==c.file_sha(cap/'inputs'/row['owner_file'])
profiles=c.axiom_profiles((d/'stage-3.stdout').read_text(encoding='utf-8')+'\n'+(d/'stage-3.stderr').read_text(encoding='utf-8'))
stages=[int((d/f'stage-{i}.native-exit').read_text()) for i in range(4)]
bad_axioms={n:profiles.get(n) for n in requests if n not in profiles or not set(profiles[n])<=c.STANDARD_AXIOMS}
warnings=[r for r in rows if (r['owned_above_frozen_baseline'] or r['inherited_above_frozen_baseline'])]
value={'run':run.name,'prior_original_accepted68_native_gates_green':all(x==0 for x in stages) and not missing and not warnings and not bad_axioms,'prior_four_stage_exits':stages,'original_requested_axioms':len(requests),'axiom_profiles':profiles,'bad_or_missing_axioms':bad_axioms,'project_closure_sources':len(closure),'project_closure':sorted(closure),'missing_compiled_objects':missing,'warning_regressions':warnings,'cache_objects_unchanged':400,'accepted':False,'helper_credit':0,'scope':'Prior original A8/A11/A7/A12/A19 accepted68 refreshed; exact frozenreview lineage retained. New A20/A21 and criticalA17/A18 profiles remain separate.'}
value['current_capture_owner_identities']=current_owners
c.write_new(run/'prior-original68-native-gates.json',c.json_bytes(value))
print(json.dumps({k:v for k,v in value.items() if k not in ['project_closure','axiom_profiles','warning_regressions']},indent=2))
