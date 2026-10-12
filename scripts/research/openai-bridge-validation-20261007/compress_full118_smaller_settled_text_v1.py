"""Bounded reversible compression of settled custody-pinned evidence only."""
import json,sys,subprocess,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full116_settled_text_v1 import allocated,digest
BASE=Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)
def main():
 rows={};parents=[]
 candidate=H/'full118-smaller-settled-text-candidates-v1.json'
 parents.append(dict(path=str(candidate),sha256=digest(candidate)))
 for r in json.loads(candidate.read_bytes())['files']:
  f=Path(r['path']);ip=Path(r['custody_index']);j=json.loads(ip.read_bytes())
  matches=[x for x in j['files'] if x.get('original',x.get('path'))==str(f)]
  assert len(matches)==1 and matches[0]['sha256']==r['sha256'] and matches[0]['bytes']==r['bytes']
  assert f.is_file() and f.resolve(strict=True)==f.absolute() and f.is_relative_to(BASE)
  assert not any(q.is_symlink() for q in [f,*f.parents] if q.is_relative_to(BASE))
  assert 'full118-' not in str(f) and ('settled-cache-recovery-v1' in str(f) or ('research-resume-20261011' in str(f) and f.name=='approved-plan.json'))
  assert digest(f)==r['sha256'] and f.stat().st_size==r['bytes'];f.read_bytes().decode('utf-8')
  rows[str(f)]=dict(path=str(f),bytes=r['bytes'],sha256=r['sha256'],allocated_before=allocated(f),custody_index=str(ip),custody_index_sha256=digest(ip))
 rows=list(rows.values());assert 0<len(rows)<=100 and sum(r['bytes'] for r in rows)<100*1024**2
 d=H/'full118-smaller-settled-text-compression-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
 (d/'plan.json').write_text(json.dumps(dict(files=rows,parents=parents,authorization='Prior root authorization for reversible byte-preserving settled text compression',deletion=False),indent=2)+'\n',encoding='utf-8')
 before=shutil.disk_usage(BASE).free;commands=[]
 for i in range(0,len(rows),12):
  group=rows[i:i+12]
  for r in group:assert digest(Path(r['path']))==r['sha256']
  x=subprocess.run(['C:/Windows/System32/compact.exe','/C','/I','/Q',*[r['path'] for r in group]],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
  (d/f'{i}.stdout').write_bytes(x.stdout);(d/f'{i}.stderr').write_bytes(x.stderr);commands.append(dict(native_exit=x.returncode));assert x.returncode==0
 for r in rows:
  f=Path(r['path']);assert digest(f)==r['sha256'] and f.stat().st_size==r['bytes'];r['allocated_after']=allocated(f)
 receipt=dict(files=rows,parents=parents,commands=commands,all_byte_hashes_unchanged=True,files_deleted=False,cloud_operation=False,compiler_invoked=False,free_before=before,free_after=shutil.disk_usage(BASE).free,reclaimed_allocated_bytes=sum(r['allocated_before']-r['allocated_after'] for r in rows))
 (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:receipt[k] for k in ['free_before','free_after','reclaimed_allocated_bytes']}))
if __name__=='__main__':main()
