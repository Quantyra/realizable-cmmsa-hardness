from pathlib import Path
import io,json,tarfile
from custody_checks import digest
from full119_recovery_stage_gate_v1 import verify_binding
H=Path(__file__).resolve().parent
OUT=H/'full119-recovery-stage-offline-negatives-v2'
VM='7237681467779354904'
def fixture(name):
 d=OUT/name;d.mkdir();root=d/'root';root.mkdir();audit=d/'audit.json';custody=d/'index.json';payload=d/'payload.tar.gz'
 r=dict(all_rows_match=True,compiler_invoked=False,power_operation=False,disk_available_bytes=40*1024**3,state=dict(id=VM,status='RUNNING'),offline_fixture_only=True)
 if name=='wrong-vm':r['state']['id']='foreign'
 if name=='wrong-state':r['state']['status']='TERMINATED'
 if name=='below-reserve':r['disk_available_bytes']-=1
 raw=(json.dumps(r,indent=2)+'\n').encode();audit.write_bytes(raw)
 with tarfile.open(payload,'w:gz') as t:
  b=b'changed retained audit' if name=='retained-audit-mismatch' else raw
  info=tarfile.TarInfo('audit.json');info.size=len(b);t.addfile(info,io.BytesIO(b))
  if name=='duplicate-member':t.addfile(info,io.BytesIO(b))
 row=dict(original=str(audit),member='audit.json',bytes=len(raw),sha256=digest(audit));j=dict(all_selected_plans_verified=True,execution_included=True,all_members_roundtrip_verified=True,files=[row],payload=dict(file=payload.name,bytes=payload.stat().st_size,sha256=digest(payload)))
 if name=='unverified-custody':j['all_members_roundtrip_verified']=False
 if name=='missing-audit-row':j['files']=[]
 if name=='ambiguous-audit-row':j['files']=[row,row]
 if name!='missing-custody':custody.write_text(json.dumps(j,indent=2)+'\n',encoding='utf8')
 if name=='altered-audit':audit.write_bytes(raw+b' ')
 if name=='altered-payload':payload.write_bytes(payload.read_bytes()+b' ')
 if name=='launch-marker':(root/'launch-once.json').write_bytes(b'{}')
 return root,audit,custody

def main():
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
 for n in ['full119_recovery_stage_gate_v1.py','stage_full119_openssh_v2.py',Path(__file__).name]:(OUT/n).write_bytes((H/n).read_bytes())
 rows=[]
 for name in ['valid','missing-custody','unverified-custody','altered-audit','altered-payload','wrong-vm','wrong-state','below-reserve','launch-marker','missing-audit-row','ambiguous-audit-row','retained-audit-mismatch','duplicate-member']:
  args=fixture(name)
  try:
   verify_binding(*args,VM)
  except (AssertionError,FileNotFoundError) as e:
   assert name!='valid';rows.append(dict(case=name,accepted=False,expected=True,rejection_type=type(e).__name__,rejection=str(e)))
  else:
   assert name=='valid','Negative fixture wrongly accepted: '+name
   rows.append(dict(case=name,accepted=True,expected=True))
 report=dict(checks=rows,all_expected_results=True,offline_fixture_only=True,lean_executed=False,cloud_operation=False,accepted=False,source_sha256={n:digest(H/n) for n in ['full119_recovery_stage_gate_v1.py','stage_full119_openssh_v2.py',Path(__file__).name]})
 (OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(checks=len(rows),all_expected_results=True,result_sha256=digest(OUT/'result.json'))))
if __name__=='__main__':main()
