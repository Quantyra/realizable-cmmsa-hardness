"""Reversible compression of exact closed Full118 native outputs, archive bytes retained."""
import json,tarfile,subprocess,shutil,sys
from pathlib import Path
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from compress_full116_settled_text_v1 import allocated,digest
ROOT=Path('C:/Users/dfred/.quantyra/builder02/full118-exact-real-complex-operators-repair8-resource02')
CHECK=ROOT/'checks/20261012T023543679265Z'
def main():
 receipt=json.loads((CHECK/'terminal-custody.json').read_bytes());assert receipt['terminal']['native_terminal']
 stop=json.loads((CHECK/'vm-termination.json').read_bytes());assert stop['independent']['status']=='TERMINATED' and str(stop['independent']['id'])=='7237681467779354904'
 for p in [Path(receipt['custody']['short_path']),Path(receipt['custody']['repository_path'])]:assert digest(p)==receipt['custody']['remote_sha256']
 plan=json.loads((H/'full118-closed-native-text-candidates-v1.json').read_bytes());rows=plan['files'];assert len(rows)==11 and plan['native_archive_sha256']==receipt['custody']['remote_sha256']
 archive=Path(receipt['custody']['repository_path'])
 with tarfile.open(archive,'r:gz') as t:
  for r in rows:
   p=Path(r['path']);assert p.resolve(strict=True)==p and p.is_relative_to(CHECK) and 'remote-evidence' in p.parts and not p.is_symlink();b=p.read_bytes();assert len(b)==r['bytes'] and b==t.extractfile(r['member']).read();b.decode('utf-8');r['sha256']=digest(p);r['allocated_before']=allocated(p)
 d=H/'full118-closed-native-output-text-compression-v1';d.mkdir(exist_ok=False);(d/'.gitattributes').write_bytes(b'* -text\n');(d/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());before=shutil.disk_usage(H).free
 x=subprocess.run(['C:/Windows/System32/compact.exe','/C','/I','/Q',*[r['path'] for r in rows]],capture_output=True,creationflags=subprocess.CREATE_NO_WINDOW);(d/'stdout').write_bytes(x.stdout);(d/'stderr').write_bytes(x.stderr);assert x.returncode==0
 with tarfile.open(archive,'r:gz') as t:
  for r in rows:
   p=Path(r['path']);assert digest(p)==r['sha256'] and p.stat().st_size==r['bytes'];assert p.read_bytes()==t.extractfile(r['member']).read();r['allocated_after']=allocated(p)
 for p in [Path(receipt['custody']['short_path']),archive]:assert digest(p)==receipt['custody']['remote_sha256']
 j={'files':rows,'free_before':before,'free_after':shutil.disk_usage(H).free,'reclaimed_allocated_bytes':sum(r['allocated_before']-r['allocated_after'] for r in rows),'all_byte_hashes_unchanged':True,'native_archive_sha256':receipt['custody']['remote_sha256'],'two_original_archives_unchanged':True,'native_terminal':True,'independent_vm_stopped':True,'audit_original_terminal':1,'files_deleted':False,'source_or_input_modified':False,'compiler_invoked':False,'cloud_action':False};(d/'receipt.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps({'sha256':digest(d/'receipt.json'),'reclaimed':j['reclaimed_allocated_bytes'],'free':j['free_after']}))
if __name__=='__main__':main()
