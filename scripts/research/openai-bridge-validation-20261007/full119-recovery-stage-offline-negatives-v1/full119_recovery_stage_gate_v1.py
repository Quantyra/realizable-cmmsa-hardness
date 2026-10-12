import json,tarfile
from pathlib import Path
from custody_checks import digest

def verify_binding(root,audit_path,custody_path,vm_id):
 root=Path(root);audit_path=Path(audit_path);custody_path=Path(custody_path)
 assert not (root/'launch-once.json').exists(),'Full119 already launched'
 report=json.loads(audit_path.read_bytes());preserved=json.loads(custody_path.read_bytes())
 assert all(preserved[k] is True for k in ('all_selected_plans_verified','execution_included','all_members_roundtrip_verified')),'Unverified recovery custody'
 assert report['all_rows_match'] is True and report['compiler_invoked'] is False and report['power_operation'] is False
 payload=custody_path.parent/preserved['payload']['file']
 assert digest(payload)==preserved['payload']['sha256'] and payload.stat().st_size==preserved['payload']['bytes'],'Recovery payload changed'
 matches=[r for r in preserved['files'] if r['original']==str(audit_path)];assert len(matches)==1,'Missing or ambiguous retained audit'
 row=matches[0];assert digest(audit_path)==row['sha256'] and audit_path.stat().st_size==row['bytes'],'Audit changed'
 with tarfile.open(payload,'r:gz') as archive:
  assert len(archive.getnames())==len(set(archive.getnames())),'Duplicate custody member'
  member=archive.getmember(row['member']);assert member.isfile()
  assert archive.extractfile(member).read()==audit_path.read_bytes(),'Retained audit mismatch'
 assert report['disk_available_bytes']>=40*1024**3,'Capacity below unchanged guard'
 assert report['state']['status']=='RUNNING' and str(report['state']['id'])==str(vm_id),'Wrong VM identity or state'
 return report
