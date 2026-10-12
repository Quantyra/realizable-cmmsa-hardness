"""Reversible compression of four settled historical metadata files, exact retained bytes."""
import json,hashlib,tarfile,subprocess,shutil,sys
from pathlib import Path
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full116_settled_text_v1 import allocated,digest
BASE=Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)
def main():
 plan=json.loads((H/'full118-closed-manifest-compression-candidates-v1.json').read_bytes());assert len(plan['files'])==4
 rows=plan['files']
 for r in rows:
  p=Path(r['path']);a=Path(r['retained_archive']);assert p.resolve(strict=True)==p and p.is_relative_to(BASE) and p.name=='capture-manifest.json' and 'full118-' not in str(p) and 'full119-' not in str(p)
  assert not p.is_symlink() and not any(q.is_symlink() for q in p.parents if q.is_relative_to(BASE));assert digest(p)==r['sha256'] and p.stat().st_size==r['bytes'];r['archive_sha256']=digest(a);r['allocated_before']=allocated(p)
  with tarfile.open(a,'r:gz') as t:assert t.extractfile(r['member']).read()==p.read_bytes()
 d=H/'full118-closed-manifest-text-compression-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());before=shutil.disk_usage(H).free
 x=subprocess.run(['C:/Windows/System32/compact.exe','/C','/I','/Q',*[r['path'] for r in rows]],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW);(d/'stdout').write_bytes(x.stdout);(d/'stderr').write_bytes(x.stderr);assert x.returncode==0
 for r in rows:
  p=Path(r['path']);assert digest(p)==r['sha256'] and p.stat().st_size==r['bytes'];assert digest(Path(r['retained_archive']))==r['archive_sha256'];r['allocated_after']=allocated(p)
  with tarfile.open(r['retained_archive'],'r:gz') as t:assert t.extractfile(r['member']).read()==p.read_bytes()
 j={'files':rows,'free_before':before,'free_after':shutil.disk_usage(H).free,'reclaimed_allocated_bytes':sum(r['allocated_before']-r['allocated_after'] for r in rows),'all_metadata_bytes_unchanged':True,'retained_input_archives_unchanged':True,'no_current_input_or_source_modified':True,'files_deleted':False,'compiler_invoked':False,'cloud_action':False,'native_exit':x.returncode}
 (d/'receipt.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps({'sha256':digest(d/'receipt.json'),'reclaimed':j['reclaimed_allocated_bytes'],'free':j['free_after']}))
if __name__=='__main__':main()
