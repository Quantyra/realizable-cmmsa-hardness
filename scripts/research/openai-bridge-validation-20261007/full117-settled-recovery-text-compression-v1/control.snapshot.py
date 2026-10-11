"""Reversible compression of six independently preserved settled transports."""
import json,shutil,subprocess
from pathlib import Path
from compress_full116_settled_text_v1 import digest,allocated
H=Path(__file__).resolve().parent
R=Path('C:/Users/dfred/.quantyra/builder02/full116-exact-real-complex-operators-repair6-resource02/settled-cache-recovery-v1').resolve(strict=True)
FILES=['openssh-plan-20261011T224551868194Z/transport/007.stdout','openssh-execute-20261011T225809978438Z/transport/007.stdout','openssh-plan-20261011T224551868194Z/transport/004.stdout','openssh-execute-20261011T225809978438Z/transport/004.stdout','complete-audit-v2/transport/005.stdout','complete-audit-v2/transport/002.stdout']
def main():
 index=H/'full117-recovery-complete-record-v1/index.json';j=json.loads(index.read_bytes());assert j['execution_included'] and j['all_members_roundtrip_verified']
 pins={r['original']:r for r in j['files']};rows=[]
 for n in FILES:
  p=R/n;assert p.resolve(strict=True)==p.absolute() and p.is_file() and not p.is_symlink()
  assert not any(x.is_symlink() for x in [p,*p.parents] if x.is_relative_to(R))
  row=pins[str(p)];assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes'];p.read_bytes().decode('utf-8')
  rows.append(dict(path=str(p),bytes=p.stat().st_size,sha256=digest(p),allocated_before=allocated(p)))
 assert len(rows)==6 and sum(r['bytes'] for r in rows)<48*1024**2
 d=H/'full117-settled-recovery-text-compression-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n')
 (d/'plan.json').write_text(json.dumps(dict(files=rows,complete_recovery_index_sha256=digest(index),prior_root_authorization='Reversible compression of bounded settled preserved text; no deletion, source or archive replacement.'),indent=2)+'\n',encoding='utf-8')
 (d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());before=shutil.disk_usage(R).free
 result=subprocess.run(['C:/Windows/System32/compact.exe','/C','/I','/Q',*[r['path'] for r in rows]],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW)
 (d/'stdout').write_bytes(result.stdout);(d/'stderr').write_bytes(result.stderr);assert result.returncode==0
 for r in rows:p=Path(r['path']);assert digest(p)==r['sha256'];r['allocated_after']=allocated(p)
 receipt=dict(files=rows,native_exit=result.returncode,all_byte_hashes_unchanged=True,files_deleted=False,free_before=before,free_after=shutil.disk_usage(R).free,reclaimed_allocated_bytes=sum(r['allocated_before']-r['allocated_after'] for r in rows),compiler_invoked=False,cloud_operation=False)
 (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');print(json.dumps(dict(files=6,free_after=receipt['free_after'],reclaimed_allocated_bytes=receipt['reclaimed_allocated_bytes'])))
if __name__=='__main__':main()
