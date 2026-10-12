from pathlib import Path
from datetime import datetime,timezone
import sys,shutil,json,subprocess
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
from finalize_builder02_bootstrap import SDK,FLAGS
from custody_checks import digest
R=Path('C:/Users/dfred/.quantyra/builder02/full120-exact-real-complex-operators-warning-cleanup-resource02')
def main():
 assert shutil.disk_usage(R).free>=1803550720
 f=R/'reauthenticated-state-probes'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');f.mkdir(parents=True,exist_ok=False);(f/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());records=[]
 for name,argv in [('account',[SDK,'auth','list','--format=json(account,status)']),('vm',[SDK,'compute','instances','describe','quantyra-lean-builder-02','--format=json(name,id,status,zone,machineType,networkInterfaces)',*FLAGS])]:
  assert shutil.disk_usage(R).free>=1803550720
  with (f/(name+'.stdout')).open('xb') as out,(f/(name+'.stderr')).open('xb') as err:code=subprocess.run(argv,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW).returncode
  row=dict(argv=argv,native_exit=code,stdout_sha256=digest(f/(name+'.stdout')),stderr_sha256=digest(f/(name+'.stderr')));records.append(row);(f/'commands.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf8');assert code==0
  value=json.loads((f/(name+'.stdout')).read_bytes())
  if name=='account':assert [r['account'] for r in value if r['status']=='ACTIVE']==['dfredriksen@quantyra.org']
  else:
   assert value['name']=='quantyra-lean-builder-02' and str(value['id'])=='7237681467779354904';assert value['zone'].endswith('/us-central1-a') and value['machineType'].endswith('/e2-highmem-8');assert not any(n.get('accessConfigs') for n in value['networkInterfaces'])
   print(json.dumps(dict(folder=str(f),vm_status=value['status'],vm_id=value['id'],account_verified=True,free_bytes=shutil.disk_usage(R).free)))
if __name__=='__main__':main()
