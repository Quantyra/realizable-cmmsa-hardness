"""Preserve original failed capacity audit; never relabel its terminal."""
from pathlib import Path
import json,tarfile,gzip,hashlib,io
H=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 root=Path('C:/Users/dfred/.quantyra/builder02');a=root/'full117-exact-real-complex-operators-repair7-resource02/settled-cache-recovery-v1/complete-audit-v2';w=root/'full118-exact-real-complex-operators-repair8-resource02/research-resume-20261011/20261012T013347352693Z-26c9d2206a10'
 c=json.loads((w/'command.json').read_bytes());assert c['native_exit']==1 and c['pid']==2020
 for n in ['stdout','stderr']:assert sha((w/n).read_bytes())==c[n+'_sha256']
 capacity=json.loads((a/'transport/049.stdout').read_bytes());assert capacity['disk_available_bytes']==42516672512<40*1024**3
 d=H/'full118-failed-recovery-capacity-audit-record-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[];archive=d/'complete-originals.tar.gz'
 with archive.open('xb') as f:
  with gzip.GzipFile(filename='',fileobj=f,mode='wb',mtime=0) as z:
   with tarfile.open(fileobj=z,mode='w') as t:
    for i,p in enumerate(sorted([q for folder in [a,w] for q in folder.rglob('*') if q.is_file()]+[Path(__file__)])):
     b=p.read_bytes();name=str(i)+'-'+p.name;info=tarfile.TarInfo(name);info.size=len(b);t.addfile(info,io.BytesIO(b));rows.append(dict(original=str(p),member=name,bytes=len(b),sha256=sha(b)))
 with tarfile.open(archive) as t:
  for r in rows:
   b=t.extractfile(r['member']).read();assert sha(b)==r['sha256'] and len(b)==r['bytes'] and sha(Path(r['original']).read_bytes())==r['sha256']
 j=dict(files=rows,original_handle=70325,original_pid=2020,native_exit=1,terminal_tool_chunk='109547',failed_gate='final remote capacity >=40GiB',remote_free_bytes=42516672512,required_bytes=40*1024**3,shortfall_bytes=40*1024**3-42516672512,all16journal_checks_reached_before_capacity_failure=True,original_failed_audit_unchanged=True,payload=dict(file=archive.name,bytes=archive.stat().st_size,sha256=sha(archive.read_bytes())),roundtrip_verified=True,compiler_invoked=False,accepted=False)
 (d/'index.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(sha((d/'index.json').read_bytes()))
if __name__=='__main__':main()
