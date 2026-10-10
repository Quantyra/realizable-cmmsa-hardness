"""Measured settled duplicate scopes for Full105 trace; no VM power or probe."""
import ast,json,sys
from pathlib import Path
from custody_checks import digest,verify_local_custody
HERE=Path(__file__).parent
SCOPES=['full105-actual-consumer-exact-energy-repair-resource02','full86-resource02']
def main(write=False):
 rows=[]
 for i,resource in enumerate(SCOPES,1):
  parent=Path('C:/Users/dfred/.quantyra/builder02')/resource
  marker=json.loads((parent/'launch-once.json').read_bytes());check=Path(marker['preflight'])
  terminal=json.loads((check/'terminal-custody.json').read_bytes());custody=terminal['custody']
  stop=json.loads((check/'vm-termination.json').read_bytes())
  verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
  assert marker['run']==terminal['run']==stop['run'] and terminal['terminal']['native_terminal']
  assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
  name='full105_trace_cache_repoint_v'+str(i)+'.py';remote='full105-trace-cache-repoint-v'+str(i)
  template=HERE/'full100_trace_cache_repoint_v5.py';text=template.read_text(encoding='utf-8')
  for field,value in [('RUN',repr(marker['run'])),('CONTROL',"HOME / "+repr(remote)),('MANIFEST_SHA',repr(digest(parent/'capture-manifest.json'))),('ARCHIVE_SHA',repr(custody['remote_sha256']))]:
   old=next(line for line in text.splitlines() if line.startswith(field+' = '));assert text.count(old)==1;text=text.replace(old,field+' = '+value)
  text=text.replace('full100','full105').replace('Full100','Full105')
  runner=(HERE/'run_full100_trace_cache_repoint_v5.py').read_text(encoding='utf-8').replace('full100','full105').replace('Full100','Full105').replace('full105-trace-cache-repoint-v5',remote).replace('full105_trace_cache_repoint_v5.py',name)
  text=text.replace('full105-consumption-v2','full105-consumption-v3')
  runner=runner.replace('full105_consumption_v2','full105_consumption_v3').replace('full105-consumption-v2','full105-consumption-v3')
  for filename,data in [(name,text),('run_'+name,runner)]:
   ast.parse(data);p=HERE/filename
   if write:p.open('xb').write(data.encode())
   else:assert p.read_bytes()==data.encode()
   rows.append(dict(path=filename,sha256=digest(p),settled_resource=resource,run=marker['run'],archive_sha256=custody['remote_sha256'],manifest_sha256=digest(parent/'capture-manifest.json')))
 record=dict(schema='full105-trace-two-settled-five-GiB-scope-derivation-v1',controls=rows,targets_GiB=[5,5],all_per_file_identity_archive_root_process_once_rollback_reversibility_guards_preserved=True,power_operations=False,probe_invoked=False,accepted=False)
 p=HERE/'full105-trace-cache-recovery-derivation.json';data=(json.dumps(record,indent=2)+'\n').encode()
 if write:p.open('xb').write(data)
 else:assert p.read_bytes()==data
 print('Two measured5GiB settled scopes preserve complete per-file transaction guards')
if __name__=='__main__':
 assert sys.argv[1:] in ([],['--write']);main(sys.argv[1:]==['--write'])
