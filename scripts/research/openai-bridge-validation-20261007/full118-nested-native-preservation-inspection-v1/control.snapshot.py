"""Read-only complete nested native preservation candidates; no cleanup authorization."""
import json,hashlib,tarfile,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def digest(f):
 h=hashlib.sha256();n=0
 while True:
  b=f.read(1024*1024)
  if not b:break
  h.update(b);n+=len(b)
 return h.hexdigest().upper(),n
def disksha(p):
 with p.open('rb') as f:return digest(f)
def main():
 d=H/'full118-nested-native-preservation-inspection-v1';d.mkdir(exist_ok=False);rows=[]
 for i in range(111,119):
  p=H/(f'full{i}-resume-failed-native-v1' if i<=114 else f'full{i}-native-final-custody-v1')/'index.json'
  raw=p.read_bytes();j=json.loads(raw);c=j['terminal_receipt']['custody'];target=Path(c['repository_path']);expected=c['repository_sha256'];size=c['bytes']
  assert j['terminal_receipt']['terminal']['native_terminal']
  stop=j.get('independent_stop',j.get('historical_independent_termination'));assert stop and stop['independent']['status']=='TERMINATED' and stop['independent']['id']=='7237681467779354904'
  a=p.parent/j['payload']['file'];assert disksha(a)==(j['payload']['sha256'],j['payload']['bytes']);assert disksha(target)==(expected,size)
  rr=[r for r in j['files'] if r['original']==str(target)];assert len(rr)==1;r=rr[0];assert (r['sha256'],r['bytes'])==(expected,size)
  members=[]
  with tarfile.open(a,'r:gz') as t:
   entry=t.getmember(r['member']);assert entry.isfile() and entry.size==size;assert digest(t.extractfile(entry))==(expected,size)
  with tarfile.open(a,'r:gz') as t:
   with tarfile.open(fileobj=t.extractfile(r['member']),mode='r|gz') as nt:
    for m in nt:
     assert m.isfile() or m.isdir()
     if m.isfile():
      q,n=digest(nt.extractfile(m));assert n==m.size;members.append(dict(member=m.name,bytes=n,sha256=q))
  with tarfile.open(target,'r:gz') as nt:
   flat=[]
   for m in nt:
    if m.isfile():
     q,n=digest(nt.extractfile(m));flat.append(dict(member=m.name,bytes=n,sha256=q))
  assert members==flat
  (d/f'full{i}-complete-native-members.json').write_text(json.dumps(members,indent=2)+'\n',encoding='utf-8')
  row=dict(remove_candidate=str(target),bytes=size,sha256=expected,retained_payload=str(a),retained_payload_sha256=j['payload']['sha256'],retained_payload_bytes=j['payload']['bytes'],retained_member=r['member'],retained_native_member_list_sha256=sha((d/f'full{i}-complete-native-members.json').read_bytes()),retained_native_member_count=len(members),historical_index=str(p),historical_index_sha256=sha(raw),historical_terminal_preserved=True,historical_independent_stop_preserved=True,post_cleanup_copies='one complete native archive nested in unchanged portable payload; no standalone archive at removed path')
  # Retain the current Full118 repository flat copy, as requested. Only its short duplicate is a candidate.
  if i==118:
   short=Path(c['short_path']);assert disksha(short)==(expected,size);row['remove_candidate']=str(short);row['retained_flat_archive']=str(target);row['post_cleanup_copies']='one retained flat archive plus byte-identical nested complete archive'
  rows.append(row);print(i,size,len(members),flush=True)
 result=dict(read_only=True,approval_received=False,files_deleted=False,candidates=rows,total_candidate_bytes=sum(r['bytes'] for r in rows),free_bytes=shutil.disk_usage(H).free,strong_reserve_bytes=1803550720,current_full118_flat_copy_retained=True,original_gates_and_receipts_unchanged=True,resolver_required_before_any_cleanup=True)
 (d/'inspection.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());print('inspection_sha256',sha((d/'inspection.json').read_bytes()))
if __name__=='__main__':main()
