"""Exact read-only remaining settled generated-cache inventory, no compiler or cleanup."""
from pathlib import Path
import ast,json,hashlib,sys
from datetime import datetime,timezone
from custody_checks import digest
from full120_builder02_controller import ROOT,VM_ID
from full114_dedicated_openssh_v2 import Session
H=Path(__file__).resolve().parent
def main():
 assert not (ROOT/'launch-once.json').exists()
 scopes=[]
 for number in tuple(range(109,120)):
  resource,=[p for p in ROOT.parent.glob('full'+str(number)+'-*') if (p/'launch-once.json').is_file()]
  m=json.loads((resource/'launch-once.json').read_bytes());c=Path(m['preflight']);t=json.loads((c/'terminal-custody.json').read_bytes());stop=json.loads((c/'vm-termination.json').read_bytes())
  assert m['run']==t['run']==stop['run'];assert t['terminal']['native_terminal'] and stop['custody_verified_before_stop'] and stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])==VM_ID
  scopes.append(dict(number=number,run=m['run']))
 source=H/'start_inspect_full120_owned_capacity_v1.py';tree=ast.parse(source.read_bytes());node=next(n for n in ast.walk(tree) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='guest' for t in n.targets));guest=node.value.func.value.value;assert guest.count("print(json.dumps({'scopes':results,'disk_available_bytes':shutil.disk_usage(home).free,'read_only':True,'compiler_invoked':False}))")==1;guest=guest.replace("print(json.dumps({'scopes':results,'disk_available_bytes':shutil.disk_usage(home).free,'read_only':True,'compiler_invoked':False}))","for scope,result in zip(SCOPES,results):\n root=home/scope['run']/'.lake/build';groups={}\n for parent,dirs,files in os.walk(root,followlinks=False):\n  for name in files:\n   p=Path(parent)/name;st=p.lstat();rel=p.relative_to(root);parts=rel.parts\n   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:continue\n   if {'lib','lean'}<=set(parts) and name.endswith(('.olean','.olean.private','.olean.server','.ilean','.olean.hash')):kind='project-lean-objects'\n   elif ('ir' in parts and name.endswith(('.c','.c.o.export','.setup.json'))) or ({'lib','lean'}<=set(parts) and name.endswith('.ir')):kind='project-generated-ir'\n   else:continue\n   g=groups.setdefault(kind,{'files':0,'allocated_bytes':0});g['files']+=1;g['allocated_bytes']+=st.st_blocks*512\n result['project_groups']=groups\nprint(json.dumps({'scopes':results,'disk_available_bytes':shutil.disk_usage(home).free,'read_only':True,'compiler_invoked':False}))").replace('SCOPES',repr(scopes))
 folder=ROOT/'remaining-generated-inventory-v2';folder.mkdir(exist_ok=False);(folder/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());(folder/'guest.snapshot.py').write_bytes(guest.encode());(folder/'scope.json').write_bytes(json.dumps(scopes,indent=2).encode())
 with Session(folder/'transport') as session:
  session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active')
  result=json.loads(session.python(guest).read_bytes());assert result['read_only'] and not result['compiler_invoked'];(folder/'inspection.json').write_bytes((json.dumps(result,indent=2)+'\n').encode())
  session.ssh('set -e; date +%s | sudo tee /var/lib/quantyra-idle-shutdown/last-active')
 print(json.dumps(dict(folder=str(folder),inspection=result)),flush=True)
if __name__=='__main__':main()
