"""Retain one explicitly owned Full120 action through terminal with exact actual custody pins."""
from datetime import datetime,timezone
from pathlib import Path
import subprocess,sys,json,uuid
from custody_checks import digest
from full120_builder02_controller import ROOT
H=Path(__file__).resolve().parent
ALLOWED={'run_full120_cache_recovery_v3.py','run_full120_cache_recovery_v2.py','audit_full120_cache_recovery_v1.py','preserve_full120_recovery_v1.py','prepare_builder02_full120_v2.py','derive_full120_controls_v1.py','validate_full120_execution_controls_v1.py','validate_full120_execution_controls_v2.py','full120_capture_gates.py','start_inspect_full120_owned_capacity_v1.py','stage_full120_openssh_v1.py','run_full120_native_openssh_v1.py','terminate_full120_after_custody_openssh_v1.py','full120_postprocess.py','preserve_full120_native_phase_v1.py','inspect_full120_earlier_settled_capacity_v1.py','inspect_full120_earlier_settled_capacity_v2.py'}
def main():
 name,*args=sys.argv[1:];assert name in ALLOWED;source=H/name;assert source.is_file()
 root=ROOT.parent/'full119-exact-real-complex-operators-repair9-resource02' if name=='prepare_builder02_full120_v2.py' else ROOT
 folder=root/'research-resume-20261011'/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'-'+uuid.uuid4().hex[:12]);folder.mkdir(parents=True,exist_ok=False)
 for s in [source,Path(__file__).resolve(),H/'full119_authorized16_nested_custody_v3.py',H/'full119_pending16_nested_custody_v2.py',H/'full118_consolidated_preservation_resolver_v1.py',H/'full118_authorized11_custody_v2.py',H/'full118_pending11_custody_v1.py',H/'full118_authorized39_custody_v2.py',H/'full118_pending39_custody_v1.py',H/'full115_cumulative_actual_receipts_v1.py',H/'full115_cumulative_cleanup_custody_v2.py']:
  (folder/s.name).write_bytes(s.read_bytes())
 for scope,base,names in [('actual16',H/'full118-approved16-cleanup-execution-v1',['approved-plan.json','authorization.json','receipt.json']),('actual11',H/'full118-approved11-cleanup-execution-v1',['receipt.json']),('actual39',H/'full118-approved39-cleanup-continuation-v2',['approved-plan.json','authorization.json','receipt.json']),('actual18',H/'full115-authorized-additional18-cleanup-20261011T1931573414476Z',['approved-plan.json','receipt.json']),('actual14',H/'full115-authorized-short-cleanup-20261011T1902419364615Z',['approved-plan.json','receipt.json'])]:
  for n in names:(folder/(scope+'-'+n)).write_bytes((base/n).read_bytes())
 (folder/'actual11-authorization.json').write_bytes((H/'full118-approved11-actual-authorization-v1/authorization.json').read_bytes())
 (folder/'actual11-plan.json').write_bytes((H/'full118-next-eleven-settled-archives-plan-v2/plan.json').read_bytes())
 code='import runpy,sys;sys.path.insert(0,sys.argv[1]);import full119_authorized16_nested_custody_v3 as a;a.activate();p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name="__main__")'
 argv=[sys.executable,'-B','-X','utf8','-c',code,str(H),str(source),*args];record=dict(argv=argv,source_sha256=digest(source),started_utc=datetime.now(timezone.utc).isoformat())
 with (folder/'stdout').open('xb') as out,(folder/'stderr').open('xb') as err:
  child=subprocess.Popen(argv,cwd=H,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW);record['pid']=child.pid;(folder/'command.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(folder=str(folder),pid=child.pid,action=[name,*args])),flush=True)
  while True:
   try:result=child.wait(timeout=30);break
   except subprocess.TimeoutExpired:print(json.dumps(dict(pid=child.pid,original_process_live=True)),flush=True)
 record.update(native_exit=result,finished_utc=datetime.now(timezone.utc).isoformat(),stdout_sha256=digest(folder/'stdout'),stderr_sha256=digest(folder/'stderr'));(folder/'command.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(folder=str(folder),native_exit=result)),flush=True);raise SystemExit(result)
if __name__=='__main__':main()
