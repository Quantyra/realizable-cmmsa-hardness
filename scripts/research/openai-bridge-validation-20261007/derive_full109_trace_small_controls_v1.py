import ast
import hashlib
import json
from pathlib import Path
from custody_checks import verify_local_custody,digest
from full109_builder02_controller import ROOT
here=Path(__file__).parent
helper_source=here/'full109_storage_cache_repoint_v3.py'
wrapper_source=here/'run_full109_trace_cache_large_native109_v1.py'
records=[]
for n,resource in [(84,'full84-resource02-warning-clean'),(85,'full85-resource02'),(86,'full86-resource02'),(87,'full87-resource02'),(88,'full88-resource02'),(89,'full89-resource02')]:
 settled=ROOT.parent/resource;marker=json.loads((settled/'launch-once.json').read_bytes());check=Path(marker['preflight'])
 native=json.loads((check/'terminal-custody.json').read_bytes());stop=json.loads((check/'vm-termination.json').read_bytes())
 assert native['run']==stop['run']==marker['run'] and native['terminal']['native_terminal']
 assert stop['custody_verified_before_stop'] and stop['independent']['status']=='TERMINATED'
 assert str(stop['independent']['id'])=='7237681467779354904'
 custody=native['custody'];verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
 manifest=digest(settled/'capture-manifest.json');archive=custody['remote_sha256']
 remote=f'full109-trace-cache-small-native{n}-v1';stem=f'full109_trace_cache_small_native{n}_v1'
 text=helper_source.read_text()
 for before,after in [('cmmsa_a8_output_20261010T081548Z_260bb38e',marker['run']),
 ('BD527227E089EC1F18C25F0B79FDE5F751C4049EC70B58CC2D3BFC62223D2FBB',manifest),
 ('2014BF04DA9758CEE67A01DBFB5746C6F24044E7DF762CD2E7746FDA89510AAF',archive),
 ('full109-storage-cache-repoint-v3',remote),
 ('full109-exact-crosslevel-warning-repair-resource02-launch-once.json','full109-consumption-v3-launch-once.json')]:
  assert before in text;text=text.replace(before,after)
 text=text.replace('Full105 v2 trace launch already exists','Full109 trace already launched')
 target=here/(stem+'.py');ast.parse(text)
 with target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(text)
 wrapper=wrapper_source.read_text().replace('full109-trace-cache-large-native109-v1',remote).replace('full109_trace_cache_large_native109_v1.py',stem+'.py')
 wrapper_target=here/('run_'+stem+'.py');ast.parse(wrapper)
 with wrapper_target.open('x',encoding='utf-8',newline='\n') as stream:stream.write(wrapper)
 records.append(dict(number=n,resource=resource,run=marker['run'],manifest=manifest,archive=archive,
  helper=target.name,helper_sha256=digest(target),controller=wrapper_target.name,controller_sha256=digest(wrapper_target),
  remote_control='/home/dfredriksen_quantyra_org/'+remote))
(here/'full109-trace-small-cache-control-derivation-v1.json').open('x').write(json.dumps(dict(scopes=records,
 target_bytes_per_scope=896*1024**2,source_project_and_canonical_files_excluded=True,
 native_qualification_not_claimed_for_failed_old_runs=True,plan_or_recovery_executed=False),indent=2)+'\n')
print(json.dumps(dict(scopes=6,settled_native_custody_and_termination_verified=True,compiler_invoked=False)))
