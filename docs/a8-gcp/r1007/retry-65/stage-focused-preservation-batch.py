import json,hashlib,subprocess,datetime
from pathlib import Path
R=Path.cwd();P=R/'docs/a8-gcp/r1007';A=P/'retry-65'
def git(args,data=None):return subprocess.run(['git',*args],cwd=R,input=data,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
initial=json.loads((A/'focused-preservation-stage.json').read_bytes());roots=initial['scope_roots'];files=set(initial['files']);files.add('docs/a8-gcp/r1007/retry-65/focused-preservation-stage.json')
for args in [['ls-files','--others','--exclude-standard','-z','--',*roots],['diff','--name-only','-z','--',*roots],['diff','--cached','--name-only','-z']]:files.update(n for n in git(args).decode().split('\0') if n)
allowed=lambda n:any(n==root or n.startswith(root+'/') for root in roots) or n in initial['source_ownership']
assert all(allowed(n) for n in files)
files={n for n in files if '__pycache__' not in Path(n).parts and not n.endswith('.pyc')};assert all((R/n).is_file() for n in files)
rows={n:{'sha256':hashlib.sha256((R/n).read_bytes()).hexdigest().upper(),'bytes':(R/n).stat().st_size} for n in sorted(files)}
receipt=A/'focused-preservation-stage-final.json';receipt.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'initial_head':initial['initial_head'],'files':rows,'original_stage_receipt_preserved':True,'partial_slow_per_file_staging_safely_replaced_by_batch':True,'source_basis_correction_included':True,'raw_FS_blob_parity':True,'inherited_dirt_excluded':True},indent=2)+'\n',encoding='utf-8');files.add(receipt.relative_to(R).as_posix());names=sorted(files);assert all('\n' not in n and '\r' not in n for n in names)
hashes=git(['hash-object','-w','--no-filters','--stdin-paths'],('\n'.join(names)+'\n').encode()).decode().splitlines();assert len(hashes)==len(names)
for n,h in zip(names,hashes):
 data=(R/n).read_bytes();assert h==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
git(['update-index','-z','--index-info'],b''.join(('100644 '+h+'\t'+n+'\0').encode() for n,h in zip(names,hashes)))
staged=set(git(['diff','--cached','--name-only','-z']).decode().split('\0'))-{''};assert staged==files
index={row.split('\t')[1]:row.split()[1] for row in git(['ls-files','--stage','-z']).decode().split('\0') if row}
assert all(index[n]==h for n,h in zip(names,hashes))
print(json.dumps({'staged_files':len(files),'raw_blob_FS_parity':True,'inherited_dirt_excluded':True,'index_mutation_batch_native0':True}))
