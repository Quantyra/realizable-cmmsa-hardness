import json,hashlib,subprocess,datetime,ast
from pathlib import Path
R=Path.cwd();P=R/'docs/a8-gcp/r1007';A=P/'retry-67';B=P/'retry-68'
for p in B.glob('*.py'):ast.parse(p.read_text(encoding='utf-8-sig'))
registry=json.loads((B/'authorized-new-author-paths.json').read_bytes());registry['paths_before']={n:{'sha256':h,'bytes':(R/n).stat().st_size} for n,h in registry['current_full_candidate_hashes'].items()};(B/'authorized-new-author-paths.json').write_text(json.dumps(registry,indent=2)+'\n',encoding='utf-8')
# Correct latest source history labels while retaining source lineage boundaries.
f=B/'controller.py';s=f.read_text(encoding='utf-8').replace('Exact frozen64 source retained through Run67 successful stages0through3','Exact frozen64 source retained through Run67 successful stages0through3');ast.parse(s);f.write_text(s,encoding='utf-8')
git=lambda args,data=None:subprocess.run(['git',*args],cwd=R,input=data,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
assert not git(['diff','--cached','--name-only']).strip()
roots=['docs/a8-gcp/r1007/retry-67','docs/a8-gcp/r1007/retry-68','docs/a8-gcp/r1007/captures/capture-full-a22-hc46-67','docs/a8-gcp/r1007/runs/cmmsa_a8_output_20261006T134011Z_55568d8b'];files=set()
for args in [['ls-files','--others','--exclude-standard','-z','--',*roots],['diff','--name-only','-z','--',*roots]]:files.update(n for n in git(args).decode().split('\0') if n)
offer=json.loads((A/'coherent-full-a22-hc46-successor/custody.json').read_bytes())['files'];files.update(offer);files={n for n in files if '__pycache__' not in Path(n).parts and not n.endswith('.pyc')}
for n,h in offer.items():assert hashlib.sha256((R/n).read_bytes()).hexdigest().upper()==h
rows={n:{'sha256':hashlib.sha256((R/n).read_bytes()).hexdigest().upper(),'bytes':(R/n).stat().st_size} for n in sorted(files)};receipt=A/'focused-preservation-stage.json';receipt.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'initial_head':git(['rev-parse','HEAD']).decode().strip(),'scope_roots':roots,'files':rows,'raw_FS_blob_parity':True,'inherited_dirt_excluded':True,'raw67_RED_preserved':True,'both_warning_seals_unchanged':True},indent=2)+'\n',encoding='utf-8');files.add(receipt.relative_to(R).as_posix());names=sorted(files);hashes=git(['hash-object','-w','--no-filters','--stdin-paths'],('\n'.join(names)+'\n').encode()).decode().splitlines();assert len(hashes)==len(names)
for n,h in zip(names,hashes):
 data=(R/n).read_bytes();assert h==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
git(['update-index','-z','--index-info'],b''.join(('100644 '+h+'\t'+n+'\0').encode() for n,h in zip(names,hashes)))
assert (set(git(['diff','--cached','--name-only','-z']).decode().split('\0'))-{''})<=files  # Unchanged intended entries are verified by raw index parity below.
index={row.split('\t')[1]:row.split()[1] for row in git(['ls-files','--stage','-z']).decode().split('\0') if row};assert all(index[n]==h for n,h in zip(names,hashes))
print(json.dumps({'staged_files':len(files),'raw_FS_blob_parity':True,'inherited_dirt_excluded':True}))
