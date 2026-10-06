"""Wait for original remote run, recover custody, then one idle-proven stop. No compiler launch."""
import runpy,json,sys,base64,shutil
from pathlib import Path
sys.dont_write_bytecode=True
here=Path(__file__).resolve().parent
m=runpy.run_path(str(here/'controller.py'),run_name='recovery55_import'); runner=m['configure'](); c=m['common']
run=m['PACKAGE']/'runs/cmmsa_a8_output_20261006T081337Z_6df39b3b'; cap=m['PACKAGE']/'captures/capture-integrated-55'
folder=run/'recovered-controller'; folder.mkdir(exist_ok=False); (folder/'control').mkdir()
control=runner.Control(folder); control.authenticated=True
remote='/home/dfredriksen_quantyra_org/cmmsa-evidence/'+run.name+'-evidence.tar.gz'
command='date -u; ps -eo pid,ppid,etimes,comm,args | awk \'$4 == "lean" || $4 == "lake" || $4 == "python3"\'; sha256sum '+remote+'; stat -c %s '+remote
_,out,_=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command='+command],timeout=1500)
lines=out.decode().splitlines(); sha=next(x.split()[0].upper() for x in lines if remote in x and len(x.split()[0])==64); size=int(lines[-1]); block=4194304
partial=Path('C:/a8gcp/'+run.name[-8:]+'.tar.gz'); assert partial.stat().st_size==9*block
partial_pin={'bytes':partial.stat().st_size,'sha256':c.file_sha(partial),'preserved_without_overwrite':True}
c.write_new(folder/'partial-archive-before.json',c.json_bytes(partial_pin))
short=Path('C:/a8gcp/'+run.name[-8:]+'-recovered.tar.gz'); assert not short.exists()
with short.open('xb') as stream:
 with partial.open('rb') as prior:
  shutil.copyfileobj(prior,stream)
 for index in range(9,(size+block-1)//block):
  command='dd if='+remote+' bs=4194304 skip='+str(index)+' count=1 status=none | base64 -w0'
  _,out,_=control.cloud(['compute','ssh',runner.VM,'--tunnel-through-iap','--command='+command],timeout=120)
  data=base64.b64decode(out,validate=True); assert len(data)==min(block,size-index*block); stream.write(data)
  print('Preserved original archive chunk',index,len(data),flush=True)
assert sha=='4B67071AE9E98199C8DA7579F7D59B82D24747E7ADCC00155470D6169BAD1CF0'
assert short.stat().st_size==size and c.file_sha(short)==sha
assert partial.stat().st_size==partial_pin['bytes'] and c.file_sha(partial)==partial_pin['sha256']
archive=run/(run.name+'-evidence.tar.gz'); assert not archive.exists(); shutil.copyfile(short,archive); assert c.file_sha(archive)==sha
custody={'verified_utc':c.utc(),'before_stop':True,'short_path':str(short),'repository_path':str(archive),'short_sha256':sha,'repository_sha256':sha,'remote_sha256':sha,'recovery':'Original archive recovered only missingchunk9 aftertransportfailure; partialcopy preserved, no compilerrestart.'}
c.write_new(run/'custody.json',c.json_bytes(custody)); c.write_new(folder/'custody.json',c.json_bytes(custody))
compiler_attempted=True
state=control.settle()
manifest=json.loads((cap/'manifest.json').read_bytes()); before=json.loads((cap/'inherited-files-before.json').read_bytes()); status=json.loads((cap/'inherited-status-before.json').read_bytes())
terminal={'run':run.name,'capture':cap.name,'finished_utc':c.utc(),'start_attempted':True,'compiler_attempted':True,'created_resources':[],'vm_terminal_receipt':state,'evidence_archive_sha256':sha,'failure':'Original archivechunk9 transportfailed; recovery preserved rawUNPROVED terminal and exactoriginal nativeoutcome separately.','local_process_check_after':c.local_process_check(),'inherited_dirt_preserved':c.inherited_now()==before and c.inherited_status_now()==status,'inherited_preservation_scope':manifest['inherited_preservation_scope'],'local_compilation':False,'automatic_git_writes':False,'recovery_controller':str(folder.relative_to(m['PACKAGE']))}
c.write_new(run/'terminal-recovery.json',c.json_bytes(terminal)); print(json.dumps({'run':run.name,'archive_sha256':sha,'vm_status':state['status'],'inherited_dirt_preserved':terminal['inherited_dirt_preserved']},indent=2),flush=True)
