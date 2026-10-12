"""Bounded reversible compression of settled custody-pinned evidence only."""
import json,sys,subprocess,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full116_settled_text_v1 import allocated,digest
BASE=Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)
def main():
 rows={};parents=[]
 recovery=BASE/'full117-exact-real-complex-operators-repair7-resource02'/'settled-cache-recovery-v1'
 scopes=json.loads((H/'full118-cache-recovery-derivation-v2.json').read_bytes())['scopes']
 execution=list(recovery.glob('openssh-execute-*'));assert len(execution)==1
 result=execution[0]/'result.json';assert json.loads(result.read_bytes())['native_exit']==0
 parents.append(dict(path=str(result),sha256=digest(result)))
 for scope in scopes:
  records=list(execution[0].glob('operation-'+scope['number']+'.json'));assert len(records)==1
  rp=records[0];r=json.loads(rp.read_bytes());f=Path(r['local_result'])
  assert digest(f)==r['result_sha256'] and r['action']=='execute'
  receipt=json.loads(f.read_bytes());assert receipt['content_identity_verified_after_repoint'] and not receipt['compiler_invoked']
  parents.append(dict(path=str(rp),sha256=digest(rp)))
  if f.stat().st_size<=200000 or allocated(f)<f.stat().st_size:continue
  assert f.resolve(strict=True)==f.absolute() and f.is_relative_to(BASE)
  assert not any(q.is_symlink() for q in [f,*f.parents] if q.is_relative_to(BASE))
  rows[str(f)]=dict(path=str(f),bytes=f.stat().st_size,sha256=r['result_sha256'],allocated_before=allocated(f))
 rows=list(rows.values());assert 0<len(rows)<=100 and sum(r['bytes'] for r in rows)<100*1024**2
 d=H/'full118-settled-recovery-execution-text-compression-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
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
