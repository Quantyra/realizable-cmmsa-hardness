"""Wait for original remote run, recover custody, then one idle-proven stop. No compiler launch."""
import runpy,json,sys,base64,shutil
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='recovery50_import'); runner=m['configure'](); c=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T055942Z_3a1927c5'; cap=m['PACKAGE']/'captures/capture-integrated-50'
folder=run/'recovered-controller'; folder.mkdir(exist_ok=False); (folder/'control').mkdir()
control=runner.Control(folder); control.authenticated=True
remote='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run.name+'-evidence.tar.gz'
command="date -u; if test -r /proc/1446/cmdline; then tr '\\0' ' ' </proc/1446/cmdline; echo; fi; while kill -0 1446 2>/dev/null; do sleep 5; done; date -u; test -f "+remote+"; sha256sum "+remote+"; stat -c %s "+remote
_,out,_=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command='+command],timeout=1500)
lines=out.decode().splitlines(); sha=next(x.split()[0].upper() for x in lines if remote in x and len(x.split()[0])==64); size=int(lines[-1]); block=4194304
short=Path('C:/a8gcp/'+run.name[-8:]+'.tar.gz'); assert not short.exists()
with short.open('xb') as stream:
 for index in range((size+block-1)//block):
  command='dd if='+remote+' bs=4194304 skip='+str(index)+' count=1 status=none | base64 -w0'
  _,out,_=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command='+command],timeout=120)
  data=base64.b64decode(out,validate=True); assert len(data)==min(block,size-index*block); stream.write(data)
  print('Preserved original archive chunk',index,len(data),flush=True)
assert short.stat().st_size==size and c.file_sha(short)==sha
archive=run/(run.name+'-evidence.tar.gz'); assert not archive.exists(); shutil.copyfile(short,archive); assert c.file_sha(archive)==sha
custody={'verified_utc':c.utc(),'before_stop':True,'short_path':str(short),'repository_path':str(archive),'short_sha256':sha,'repository_sha256':sha,'remote_sha256':sha,'recovery':'Original remote run survived local controller interruption; no compiler restart.'}
c.write_new(run/'custody.json',c.json_bytes(custody)); c.write_new(folder/'custody.json',c.json_bytes(custody))
compiler_attempted=True
state=control.settle()
manifest=json.loads((cap/'manifest.json').read_bytes()); before=json.loads((cap/'inherited-files-before.json').read_bytes()); status=json.loads((cap/'inherited-status-before.json').read_bytes())
terminal={'run':run.name,'capture':cap.name,'finished_utc':c.utc(),'start_attempted':True,'compiler_attempted':True,'created_resources':[],'vm_terminal_receipt':state,'evidence_archive_sha256':sha,'failure':'Original local controller interrupted; recovery monitor preserved original remote native outcome separately.','local_process_check_after':c.local_process_check(),'inherited_dirt_preserved':c.inherited_now()==before and c.inherited_status_now()==status,'inherited_preservation_scope':manifest['inherited_preservation_scope'],'local_compilation':False,'automatic_git_writes':False,'recovery_controller':str(folder.relative_to(m['PACKAGE']))}
c.write_new(run/'terminal.json',c.json_bytes(terminal)); print(json.dumps({'run':run.name,'archive_sha256':sha,'vm_status':state['status'],'inherited_dirt_preserved':terminal['inherited_dirt_preserved']},indent=2),flush=True)
