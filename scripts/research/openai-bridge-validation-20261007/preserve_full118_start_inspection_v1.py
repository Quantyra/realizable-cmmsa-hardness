"""Complete portable custody of the sole terminal guarded start/inspection."""
import gzip,hashlib,json,tarfile
from pathlib import Path
H=Path(__file__).resolve().parent
R=Path('C:/Users/dfred/.quantyra/builder02/full118-exact-real-complex-operators-repair8-resource02')
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(16384),b''):h.update(b)
 return h.hexdigest().upper()
def main():
 marker=json.loads((R/'start-once.json').read_bytes());stage=Path(marker['original_start_folder'])
 wrapper=R/'research-resume-20261011/20261012T004347513261Z-7e33e69174b8';command=json.loads((wrapper/'command.json').read_bytes())
 assert command['pid']==5960 and command['native_exit']==0
 for stream in ['stdout','stderr']:assert digest(wrapper/stream)==command[stream+'_sha256']
 for i in [0,1]:
  j=json.loads((stage/f'{i}.lifecycle.json').read_bytes());assert j['native_exit']==0
  for stream in ['stdout','stderr']:assert digest(stage/f'{i}.lifecycle.{stream}')==j[stream+'_sha256']
 observation=json.loads((stage/'inspection.json').read_bytes());assert observation['read_only'] and not observation['compiler_invoked']
 files={R/'start-once.json',Path(__file__).resolve()}
 for folder in [wrapper,stage]:files.update(p for p in folder.rglob('*') if p.is_file())
 d=H/'full118-owned-capacity-inspection-record-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');rows=[]
 payload=d/'originals.tar.gz'
 with payload.open('xb') as raw,gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as gz,tarfile.open(fileobj=gz,mode='w|') as t:
  for i,p in enumerate(sorted(files)):
   assert not p.is_symlink();name=f'originals/{i:05}';t.add(p,arcname=name,recursive=False);rows.append(dict(original=str(p),member=name,bytes=p.stat().st_size,sha256=digest(p)))
 with tarfile.open(payload,'r:gz') as t:
  assert len(t.getmembers())==len(rows)
  for row in rows:
   h=hashlib.sha256();f=t.extractfile(row['member'])
   for b in iter(lambda:f.read(16384),b''):h.update(b)
   assert h.hexdigest().upper()==row['sha256']
 index=dict(files=rows,payload=dict(file=payload.name,bytes=payload.stat().st_size,sha256=digest(payload)),original_handle=23226,original_pid=5960,native_exit=0,tool_terminal_chunk='fea08a',all_members_roundtrip_verified=True,all_originals_preserved=True,one_guarded_start=True,read_only_inspection=True,compiler_invoked=False,source_scope_unchanged=True,local_required_bytes=1803550720,remote_required_bytes=42949672960,remote_observed_bytes=observation['disk_available_bytes'],admission_passed=False)
 (d/'index.json').write_text(json.dumps(index,indent=2)+'\n',encoding='utf-8');print(digest(d/'index.json'))
if __name__=='__main__':main()
