"""Contingent settled-cache recovery; preserve qualified project objects and trace gates."""
import ast
import hashlib
import json
from pathlib import Path
here=Path(__file__).parent
helper_source=here/'full109_storage_cache_repoint_v1.py'
controller_source=here/'run_full109_storage_cache_repoint_v1.py'
scopes=[dict(number=107,resource='full107-exact-product-energy-repair-resource02',
 run='cmmsa_a8_output_20261010T053442Z_835bc942',manifest='F7D8DD882D1A5FF8195CC9728166AC10D458EB18DBCD148086A3E15A2115781D',
 archive='1A0CA7DF0B4C8994CE99FAC652380B70252EB3019059898D09622CB117676368'),
 dict(number=109,resource='full109-exact-crosslevel-warning-repair-resource02',
 run='cmmsa_a8_output_20261010T110328Z_0d5c26f4',manifest='7212F8D1D98A899BA54DC3498D3E47CC3B68AAB432B3BA3B68ABA74117B8E6B4',
 archive='BD8EC70F9A138EBB5C3AC8E52B7732CF7CFE3D3E5C9B9F8CB3FB16FE37F21154')]
records=[]
for scope in scopes:
 n=scope['number'];stem=f'full109_trace_cache_large_native{n}_v1'
 remote=f'full109-trace-cache-large-native{n}-v1'
 text=helper_source.read_text()
 for before,after in [('cmmsa_a8_output_20261010T081548Z_260bb38e',scope['run']),
 ('BD527227E089EC1F18C25F0B79FDE5F751C4049EC70B58CC2D3BFC62223D2FBB',scope['manifest']),
 ('2014BF04DA9758CEE67A01DBFB5746C6F24044E7DF762CD2E7746FDA89510AAF',scope['archive']),
 ('full109-storage-cache-repoint-v1',remote),
 ('full109-exact-crosslevel-warning-repair-resource02-launch-once.json','full109-consumption-v3-launch-once.json')]:
  assert before in text;text=text.replace(before,after)
 text=text.replace('Full105 v2 trace launch already exists','Full109 consumption trace already launched')
 text=text.replace('settled full89','settled native'+str(n)).replace('Settled full89','Settled native'+str(n))
 # Original guards retain exact metadata, no compiler/copy/worker, source/archive/root pins.
 target=here/(stem+'.py');ast.parse(text)
 with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
 wrapper=controller_source.read_text()
 wrapper=wrapper.replace('full109-storage-cache-repoint-v1',remote)
 wrapper=wrapper.replace('full109_storage_cache_repoint_v1.py',stem+'.py')
 wrapper=wrapper.replace("(ROOT / 'launch-once.json')", "(ROOT / 'consumption-v3' / 'launch-once.json')")
 wrapper=wrapper.replace("ROOT / 'cache-repoint-controls'", "ROOT / 'consumption-v3' / 'cache-repoint-controls'")
 anchor='    validate_successor()';assert wrapper.count(anchor)==1
 wrapper=wrapper.replace(anchor,anchor+'\n    from full109_consumption_v3_controller import ready\n    ready()')
 wrapper_target=here/('run_'+stem+'.py');ast.parse(wrapper)
 with wrapper_target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(wrapper)
 scope.update(remote_control='/home/dfredriksen_quantyra_org/'+remote,helper=target.name,
  helper_sha256=hashlib.sha256(target.read_bytes()).hexdigest().upper(),controller=wrapper_target.name,
  controller_sha256=hashlib.sha256(wrapper_target.read_bytes()).hexdigest().upper())
 records.append(scope)
record=dict(schema='full109-qualified-trace-settled-large-cache-control-derivation-v1',scopes=records,
 helper_source_sha256=hashlib.sha256(helper_source.read_bytes()).hexdigest().upper(),
 controller_source_sha256=hashlib.sha256(controller_source.read_bytes()).hexdigest().upper(),
 target_bytes_per_scope=5*1024**3,min_bytes=65536,canonical_warm_source_read_only=True,
 source_and_project_object_and_evidence_files_excluded=True,identity_level='Current byte equality, not exhaustive capture-time cache hashes',
 plan_or_recovery_executed=False,trace_executed=False,accepted=False)
(here/'full109-trace-cache-large-control-derivation-v1.json').open('x').write(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(scopes=2,contingent_only=True)))
