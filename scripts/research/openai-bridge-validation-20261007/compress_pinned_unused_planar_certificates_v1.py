from pathlib import Path
import hashlib,json,subprocess,shutil,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full119_retired_plans_journals_ntfs_v1 import allocation
ROOT=Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
SCOPE=ROOT/'lean/OAI/Analysis/PlanarPacking/Certificate'
REV='adc7f1241b42e322a6451854ab7e4b4c146bf78a'
OUT=H/'pinned-unused-planar-certificate-ntfs-compression-v1'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
def main():
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');(OUT/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 rows=[]
 for p in sorted(SCOPE.rglob('*.lean'),key=lambda p:(-p.stat().st_size,str(p))):
  if sum(r['bytes'] for r in rows)>=120*1024*1024:break
  assert p.is_file() and not p.is_symlink() and not(p.stat().st_file_attributes&0x400)
  assert p.resolve().is_relative_to(SCOPE.resolve())
  rel=p.relative_to(ROOT).as_posix();b=p.read_bytes();b.decode('utf8')
  blob=subprocess.check_output(['git','-C',str(ROOT),'show',REV+':'+rel]);assert blob==b,rel
  oid=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',REV+':'+rel],text=True).strip()
  rows.append(dict(path=str(p),git_path=rel,git_blob=oid,bytes=len(b),sha256=sha(b),allocation_before=allocation(p)))
 assert rows
 (OUT/'frozen-positive-plan.json').write_text(json.dumps(dict(revision=REV,scope=str(SCOPE),files=rows,raw_git_bytes_verified=True,excluded_active_inputs=True),indent=2)+'\n',encoding='utf8')
 before=shutil.disk_usage(H).free;results=[]
 for i,r in enumerate(rows):
  p=Path(r['path']);b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];b.decode('utf8')
  argv=['compact.exe','/C','/Q','/I',str(p)]
  with (OUT/f'{i:03d}.stdout').open('xb') as out,(OUT/f'{i:03d}.stderr').open('xb') as err:code=subprocess.run(argv,stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW).returncode
  assert code==0;b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];b.decode('utf8')
  assert subprocess.check_output(['git','-C',str(ROOT),'show',REV+':'+r['git_path']])==b
  results.append(dict(**r,allocation_after=allocation(p),native_exit=code,raw_git_content_unchanged=True,utf8_readable=True))
 report=dict(files=results,free_before=before,free_after=shutil.disk_usage(H).free,reclaimed=sum(r['allocation_before']-r['allocation_after'] for r in results),source_contents_changed=False,deleted=False,compiler_invoked=False)
 (OUT/'receipt.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8');print(json.dumps(dict(files=len(rows),free_after=report['free_after'],reclaimed=report['reclaimed'],receipt_sha256=sha((OUT/'receipt.json').read_bytes()))))
if __name__=='__main__':main()
