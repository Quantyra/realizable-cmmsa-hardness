from pathlib import Path
import sys,json,hashlib,subprocess,shutil
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
from compress_full119_retired_plans_journals_ntfs_v1 import allocation
ROOT=Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008');REV='adc7f1241b42e322a6451854ab7e4b4c146bf78a'
PLAN=H/'pinned-unused-small-residual-cache-scopes-plan-v1/frozen-positive-plan.json';PIN='9CA536C0960F807F05DC51C04CCEA00CC1663935D145188269D543F168ADFC80';OUT=H/'pinned-unused-small-residual-cache-scopes-compression-v1'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
NAMES=['Probability/SLE', 'Geometry/SmoothYau', 'Probability/ParisiFinite', 'Combinatorics/IndependentSets', 'Probability/SKGap', 'Geometry/Borsuk', 'Probability/Perceptron', 'Combinatorics/StripMass']
def main():
 pb=PLAN.read_bytes();assert sha(pb)==PIN;plan=json.loads(pb);assert plan['revision']==REV and plan['scopes']==NAMES;assert len(plan['files'])==1508 and plan['logical_bytes']==25885255<40*1024**2
 for p,pin in plan['active_input_pins'].items():assert sha(Path(p).read_bytes())==pin
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');(OUT/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());(OUT/'frozen-positive-plan.json').write_bytes(pb)
 proc=subprocess.Popen(['git','-C',str(ROOT),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 def verify(r,initial):
  p=Path(r['path']);st=p.stat();assert p.is_file() and not p.is_symlink() and not st.st_file_attributes&0x400;assert p.resolve().is_relative_to((ROOT/'lean/OAI'/r['scope']).resolve());assert r['scope'] in NAMES and 'Computability' not in p.parts and p.suffix=='.lean';assert st.st_size==r['bytes']>=8192
  if initial:assert not st.st_file_attributes&0x800 and allocation(p)==r['allocation_before']
  b=p.read_bytes();assert sha(b)==r['sha256'] and not b.startswith(b'\xef\xbb\xbf');b.decode('utf8')
  proc.stdin.write((REV+':'+r['git_path']+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();assert header[0].decode()==r['git_blob'];size=int(header[2]);raw=proc.stdout.read(size);assert proc.stdout.read(1)==b'\n' and raw==b
 for r in plan['files']:verify(r,True)
 before=shutil.disk_usage(H).free;rows=[]
 for i in range(0,len(plan['files']),40):
  batch=plan['files'][i:i+40]
  for r in batch:verify(r,True)
  with (OUT/f'{i:04d}.stdout').open('xb') as out,(OUT/f'{i:04d}.stderr').open('xb') as err:code=subprocess.run(['compact.exe','/C','/Q','/I']+[r['path'] for r in batch],stdout=out,stderr=err,creationflags=subprocess.CREATE_NO_WINDOW).returncode
  assert code==0
  for r in batch:verify(r,False);rows.append(dict(**r,allocation_after=allocation(Path(r['path'])),native_exit=code,batch=i))
 proc.stdin.close();assert proc.wait()==0
 receipt=dict(plan_sha256=PIN,files=rows,free_before=before,free_after=shutil.disk_usage(H).free,reclaimed=sum(r['allocation_before']-r['allocation_after'] for r in rows),raw_git_bytes_verified_before_and_after=True,source_contents_changed=False,deleted=False,compiler_invoked=False)
 (OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in receipt.items() if k!='files'}));print('receipt_sha256',sha((OUT/'receipt.json').read_bytes()))
if __name__=='__main__':main()
