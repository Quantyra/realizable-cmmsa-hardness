"""Prepare exact read-only consolidated preservation plan. No deletion authority."""
import json,hashlib,tarfile,shutil
from pathlib import Path
from inspect_full118_nested_native_preservation_v1 import digest,disksha
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def checkedpath(p):
 p=Path(p);q=p.resolve();assert q.is_relative_to(Path('C:/Users/dfred/.quantyra').resolve()) or q.is_relative_to(Path('C:/a8gcp').resolve());assert p.is_file()
 for x in [p,*p.parents]:assert not x.is_symlink() and not x.is_junction()
 return q
def members(p):
 out=[]
 with tarfile.open(p,'r:gz') as t:
  for m in t:
   assert m.isfile() or m.isdir()
   if m.isfile():
    s,n=digest(t.extractfile(m));out.append(dict(member=m.name,bytes=n,sha256=s))
 return out

def main():
 d=H/'full118-consolidated-settled-preservation-plan-v2';d.mkdir(exist_ok=False);rows=[]
 ix=H/'full118-nested-native-preservation-inspection-v1/inspection.json';jr=json.loads(ix.read_bytes());assert sha(ix.read_bytes())=='350AF591EB5BFDE7C9C1751560F9E1CC2BA3769F332033A688CAE2EE71A588E3'
 for r in jr['candidates']:
  p=checkedpath(r['remove_candidate']);assert disksha(p)==(r['sha256'],r['bytes'])
  keep=checkedpath(r['retained_payload']);assert disksha(keep)==(r['retained_payload_sha256'],r['retained_payload_bytes'])
  rr=dict(kind='nested_complete_native',remove=str(p),remove_bytes=r['bytes'],remove_sha256=r['sha256'],retained_archive=str(keep),retained_archive_sha256=r['retained_payload_sha256'],retained_archive_bytes=r['retained_payload_bytes'],retained_member=r['retained_member'],historical_index=r['historical_index'],historical_index_sha256=r['historical_index_sha256'],complete_native_members_reference=str(ix.parent/('full'+Path(r['historical_index']).parent.name.split('-')[0][4:]+'-complete-native-members.json')),historical_terminal_and_independent_stop_preserved=True)
  rr['complete_native_members_reference_sha256']=sha(Path(rr['complete_native_members_reference']).read_bytes())
  if 'retained_flat_archive' in r:
   rr['retained_flat_archive']=str(checkedpath(r['retained_flat_archive']));assert disksha(Path(rr['retained_flat_archive']))==(r['sha256'],r['bytes'])
  rows.append(rr)
 flat=json.loads((H/'full118-other-settled-portable-duplicate-candidates-v1.json').read_bytes())['files']
 qindex=H/'full109-resume-qualified-trace-v1/index.json';qj=json.loads(qindex.read_bytes());r=next(r for r in qj['files'] if r['bytes']>30000000)
 flat.append(dict(path=str(qindex.parent/r['copy']),bytes=r['bytes'],sha256=r['sha256'],retained=[r['original']],index=str(qindex),index_sha256=sha(qindex.read_bytes())))
 for r in flat:
  p=checkedpath(r['path']);keep=checkedpath(r['retained'][0]);assert p!=keep;assert disksha(p)==disksha(keep)==(r['sha256'],r['bytes']);assert sha(Path(r['index']).read_bytes())==r['index_sha256']
  old=members(p);current=members(keep);assert old==current
  f=d/(f'flat-{len(rows)}-complete-members.json');f.write_text(json.dumps(current,indent=2)+'\n',encoding='utf-8')
  rows.append(dict(kind='flat_complete_duplicate',remove=str(p),remove_bytes=r['bytes'],remove_sha256=r['sha256'],retained_archive=str(keep),retained_archive_sha256=r['sha256'],retained_archive_bytes=r['bytes'],complete_native_members_reference=str(f),complete_native_members_reference_sha256=sha(f.read_bytes()),historical_index=r['index'],historical_index_sha256=r['index_sha256']))
 for r in json.loads((H/'full118-earlier-portable-member-containment-inspection-v1.json').read_bytes())['matches']:
  p=checkedpath(r['payload']);keep=checkedpath(r['retained_payload']);assert disksha(p)==(r['expected_sha256'],r['bytes']);assert disksha(keep)[0]==r['retained_expected_sha256']
  old=members(p);current=members(keep);oi=json.loads(Path(r['earlier_index']).read_bytes());ni=json.loads(Path(r['retained_index']).read_bytes());byoriginal={x['original']:x for x in ni['files']};byold={x['member']:x for x in old};bynew={x['member']:x for x in current};mapping=[]
  assert len(old)==r['member_count']==len(oi['files'])
  for x in oi['files']:
   y=byoriginal[x['original']];assert (x['bytes'],x['sha256'])==(y['bytes'],y['sha256']);assert (byold[x['member']]['bytes'],byold[x['member']]['sha256'])==(x['bytes'],x['sha256']);assert (bynew[y['member']]['bytes'],bynew[y['member']]['sha256'])==(x['bytes'],x['sha256']);mapping.append(dict(original=x['original'],retired_member=x['member'],retained_member=y['member'],bytes=x['bytes'],sha256=x['sha256']))
  old=mapping
  f=d/(f'subset-{len(rows)}-complete-members.json');f.write_text(json.dumps(old,indent=2)+'\n',encoding='utf-8')
  rows.append(dict(kind='contained_earlier_portable_payload',remove=str(p),remove_bytes=r['bytes'],remove_sha256=r['expected_sha256'],retained_archive=str(keep),retained_archive_sha256=r['retained_expected_sha256'],retained_archive_bytes=keep.stat().st_size,all_original_member_count=len(old),complete_native_members_reference=str(f),complete_native_members_reference_sha256=sha(f.read_bytes()),historical_index=r['earlier_index'],historical_index_sha256=sha(Path(r['earlier_index']).read_bytes()),retained_index=r['retained_index'],retained_index_sha256=sha(Path(r['retained_index']).read_bytes())))
 assert len({r['remove'] for r in rows})==len(rows);assert not {r['remove'] for r in rows}&{r['retained_archive'] for r in rows}
 free=shutil.disk_usage(H).free;total=sum(r['remove_bytes'] for r in rows)
 j=dict(schema='full118-consolidated-settled-preservation-plan-v2',read_only=True,explicit_approval_received=False,files_deleted=False,file_count=len(rows),total_remove_bytes=total,files=rows,fresh_free_bytes=free,projected_free_bytes=free+total,strong_reserve_bytes=1803550720,projected_margin_over_strong_reserve=free+total-1803550720,current_full118_flat_native_copy_retained=True,historical_receipts_gates_and_failures_immutable=True,prior_approval_scopes_closed=True,consumer_compatibility_pending=True,cleanup_execution_blocked_until_explicit_approval_and_successor_resolver_tests=True)
 (d/'plan.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());print(json.dumps(dict(plan_sha256=sha((d/'plan.json').read_bytes()),count=len(rows),bytes=total,projected_margin=j['projected_margin_over_strong_reserve'])))
if __name__=='__main__':main()
