"""Derive full257/focused89 controls from actual qualified Full105 native custody."""
import ast,json,re,sys,tarfile
from pathlib import Path
from custody_checks import digest,verify_local_custody
from prepare_builder02_full105 import OUTPUT
HERE=Path(__file__).parent
NAMES=[('full103_consumption_v3_controller.py','full105_consumption_v3_controller.py'),
 ('full103_consumption_v2_worker.py','full105_consumption_v3_worker.py'),
 ('stage_full103_consumption_v2.py','stage_full105_consumption_v3.py'),
 ('terminate_full103_consumption_v2.py','terminate_full105_consumption_v3.py'),
 ('qualify_full103_consumption_v2.py','qualify_full105_consumption_v3.py'),
 ('test_full103_consumption_v2_gates.py','test_full105_consumption_v3_gates.py')]
def main(write=False):
 marker=json.loads((OUTPUT/'launch-once.json').read_bytes());check=Path(marker['preflight']);receipt=json.loads((check/'terminal-custody.json').read_bytes());custody=receipt['custody'];stop=json.loads((check/'vm-termination.json').read_bytes());q=check/'qualified-native'/marker['run']/'material-expanded-native-report.json';qualified=json.loads(q.read_bytes())
 assert marker['run']==receipt['run']==stop['run'] and receipt['terminal']['compile_green']
 assert qualified['full105_expanded_native_gates_green'] and qualified['expanded_requested_axiom_count']==257
 assert qualified['owned_warning_headers']==qualified['inherited_regression_headers']==[0]*7
 assert qualified['project_closure_sources']==344 and qualified['cache_objects_unchanged']==566
 assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
 verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
 with tarfile.open(custody['repository_path']) as archive:
  objects=json.loads(archive.extractfile('object-after.json').read());manifest=json.loads(archive.extractfile('capture-manifest.json').read())
 expected={'.lake/build/lib/lean/'+p.removeprefix('lean/').removesuffix('.lean')+'.olean' for p in manifest['project_sources']}
 assert len(expected)==344 and expected<=set(objects) and len(objects)==695
 rows=[]
 for source,target in NAMES:
  text=(HERE/source).read_text(encoding='utf8')
  text=text.replace('full103-spectral-owned-warning-repair','full105-actual-consumer-exact-energy-repair')
  text=text.replace('full103_consumption_v2','full105_consumption_v3').replace('full103_consumption_v3','full105_consumption_v3')
  text=text.replace('full103','full105').replace('Full103','Full105').replace('consumption-v2','consumption-v3')
  text=text.replace('cmmsa_a8_output_20261009T220649Z_320f54a1',marker['run']).replace('320f54a1',marker['run'].rsplit('_',1)[1])
  for before,after in [('340','344'),('251','257'),('687','695'),('83','89')]:text=re.sub(r'\b'+before+r'\b',after,text)
  text=text.replace('exact251','exact257').replace('focused-eighty-three-consumer','focused-eighty-nine-consumer')
  if source=='full103_consumption_v3_controller.py':
   before='from prepare_builder02_full101 import additions as SPECTRAL_ADDITIONS';assert text.count(before)==1;text=text.replace(before,'from prepare_builder02_full104 import additions as SPECTRAL_ADDITIONS')
  ast.parse(text);path=HERE/target;data=text.encode()
  if write:path.open('xb').write(data)
  else:assert path.read_bytes()==data
  rows.append(dict(source=source,source_sha256=digest(HERE/source),target=target,target_sha256=digest(path)))
 result=dict(schema='full105-qualified-actual-run-consumption-control-derivation-v3',records=rows,run=marker['run'],native_archive_sha256=custody['remote_sha256'],qualified_report_sha256=digest(q),actual_native_object_entries=695,project_sources=344,requested_roots=257,focused_consumers=89,latest6_preparation_requests_distinguished_from_cumulative85_additional_profiles=True,parent_trace_algorithms_and_resource_source_object_dependency_guards_preserved=True,prepared_postprocess_scope_already_verified=True,compiler_invoked=False,probe_executed=False,accepted=False)
 path=HERE/'full105-consumption-control-derivation-v3.json';data=(json.dumps(result,indent=2)+'\n').encode()
 if write:path.open('xb').write(data)
 else:assert path.read_bytes()==data
 print(json.dumps(dict(controls=6,run=marker['run'],actual_object_entries=695,roots=257,focused=89)))
if __name__=='__main__':
 assert sys.argv[1:] in ([],['--write']);main(sys.argv[1:]==['--write'])
