from pathlib import Path
import hashlib,json,re,subprocess,sys,urllib.request
H=Path(__file__).resolve().parent
OUT=H/'joint-codec-minimal-source-closure-v2'
REV='6c248df7859f2f245e731c1e07057bf69d165fe2'
U=Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
UPREV='adc7f1241b42e322a6451854ab7e4b4c146bf78a'
sha=lambda b:hashlib.sha256(b).hexdigest().upper()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def get(url):
 request=urllib.request.Request(url,headers={'User-Agent':'Quantyra-pinned-source-closure'})
 with urllib.request.urlopen(request,timeout=60) as response:return response.read()
def imports(b):
 text=b.decode('utf8');lines=[];depth=0
 for line in text.splitlines():
  out='';i=0
  while i<len(line):
   if line[i:i+2]=='/-':depth+=1;i+=2
   elif depth and line[i:i+2]=='-/':depth-=1;i+=2
   elif depth:i+=1
   elif line[i:i+2]=='--':break
   else:out+=line[i];i+=1
  out=out.strip()
  if not out or out in ('prelude','module'):continue
  m=re.fullmatch(r'(?:public\s+)?import\s+(.+)',out)
  if not m:break
  lines.extend(m.group(1).split())
 return lines

def main():
 OUT.mkdir(exist_ok=False);(OUT/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n');(OUT/'control.snapshot.py').write_bytes(Path(__file__).read_bytes());project=OUT/'project';project.mkdir();rows=[];known={};queue=[]
 def store(module,b,provenance):
  b.decode('utf8');assert not b.startswith(bytes.fromhex('efbbbf'));path=project/(module.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.open('xb').write(b);known[module]=b;rows.append(dict(module=module,file=path.relative_to(OUT).as_posix(),bytes=len(b),sha256=sha(b),imports=imports(b),**provenance));queue.extend(imports(b))
 custom=[(1,'LocalThreeSATBinaryCodec','B8F38CE6B3DFD205CADE3DA1D7FE39D6D3AD0F7FA0B9E61B6DB98311740909F6'),(2,'LocalThreeSATBinaryCodecSemantics','2330AE0858786272F55F4174C520DA27D10DEC0D75E1A1576687A54BF86BBA1B'),(6,'LocalThreeSATBinaryCodecRuntime','9D014AC23A501326B1DA7EC322BC0B86D5DFAF93E7868D2A11A735607318FAC0'),(6,'LocalThreeSATBinaryCodecUpstream','E1521AE310672E3572F4E58AFE88BEB9DBCD801878CB4E63DCF3D728254B7F7B')]
 for version,module,pin in custom:
  d=H/('local-three-sat-binary-codec-capture-20261012-v'+str(version));b=(d/(module+'.lean')).read_bytes();assert sha(b)==pin;store(module,b,dict(kind='exact immutable custom capture',capture_index_sha256=sha((d/'index.json').read_bytes()),original=str(d/(module+'.lean'))))
 oai=H/'joint-codec-environment-source-plan-v1/upstream-sources/OAI';files=list(oai.rglob('*.lean'));assert len(files)==20
 for path in files:
  relative=path.relative_to(oai);gitpath='lean/OAI/'+relative.as_posix();b=path.read_bytes();raw=subprocess.check_output(['git','-C',str(U),'show',UPREV+':'+gitpath]);assert b==raw;module='OAI.'+'.'.join(relative.with_suffix('').parts);store(module,b,dict(kind='actual pinned OAI source',revision=UPREV,git_path=gitpath,git_blob=blob(b),original=str(path)))
 print(json.dumps(dict(custom_modules=4,OAI_modules=20,source_only=True)),flush=True)
 url='https://api.github.com/repos/SamuelSchlesinger/complexitylib/git/trees/'+REV+'?recursive=1';tree_raw=get(url);tree=json.loads(tree_raw);assert not tree.get('truncated');(OUT/'complexitylib-git-tree.json').write_bytes(tree_raw);entries={row['path']:row for row in tree['tree'] if row['type']=='blob'}
 cached={}
 d=H/'local-three-sat-binary-codec-capture-20261012-v6';index=json.loads((d/'index.json').read_bytes())
 for row in index['files']:
  name=row['copy_path']
  if name.startswith('dependency.Cobham') and name.endswith('.source'):
   middle=name[len('dependency.Cobham'): -len('.source')];module='Complexitylib.Classes.P.Cobham'+('.Internal'+middle if middle else '');b=(d/name).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes'];cached[module]=(b,str(d/name))
 external=set()
 while queue:
  module=queue.pop(0)
  if module in known:continue
  if module.startswith('OAI.'):raise AssertionError('Actual OAI closure missing '+module)
  if not module.startswith('Complexitylib.'):
   external.add(module);continue
  assert re.fullmatch(r'Complexitylib(?:\.[A-Za-z_][A-Za-z0-9_]*)+',module),module
  gitpath=module.replace('.','/')+'.lean';assert gitpath in entries,gitpath
  url='https://raw.githubusercontent.com/SamuelSchlesinger/complexitylib/'+REV+'/'+gitpath
  if module in cached:b,original=cached[module];transport='existing byte-pinned capture'
  else:b=get(url);original=url;transport='primary pinned HTTPS'
  assert blob(b)==entries[gitpath]['sha'],gitpath
  store(module,b,dict(kind='actual pinned complexitylib source',revision=REV,git_path=gitpath,git_blob=entries[gitpath]['sha'],original=original,primary_url=url,transport=transport))
  if len([r for r in rows if r['kind']=='actual pinned complexitylib source'])%10==0:print(json.dumps(dict(complexitylib_modules=sum(r['kind']=='actual pinned complexitylib source' for r in rows),pending=len(queue))),flush=True)
 configs=[]
 for name in ['lakefile.lean','lake-manifest.json','lean-toolchain','LICENSE']:
  if name not in entries:continue
  url='https://raw.githubusercontent.com/SamuelSchlesinger/complexitylib/'+REV+'/'+name;b=get(url);assert blob(b)==entries[name]['sha'];p=OUT/'original-complexitylib-configs'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(b);configs.append(dict(file=p.relative_to(OUT).as_posix(),bytes=len(b),sha256=sha(b),git_blob=entries[name]['sha'],primary_url=url))
 for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:
  gitpath='lean/'+name;b=subprocess.check_output(['git','-C',str(U),'show',UPREV+':'+gitpath]);p=OUT/'original-OAI-configs'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(b);configs.append(dict(file=p.relative_to(OUT).as_posix(),bytes=len(b),sha256=sha(b),git_blob=blob(b),revision=UPREV,git_path=gitpath))
 checks=(H/'local-three-sat-binary-codec-capture-20261012-v6/Checks.lean').read_bytes();assert sha(checks)=='BC9EF3E034F43B85AA034F90C99E7555BAB9EF68B6AD56845170DFE8EA498185';(project/'Checks.lean').write_bytes(checks)
 config='import Lake\nopen Lake DSL\npackage jointCodec\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"\nlean_lib Complexitylib where\n  roots := #[`Complexitylib.SAT.Encoding, `Complexitylib.SAT.ThreeSAT, `Complexitylib.Classes.P.Cobham, `Complexitylib.Classes.P.Cobham.Internal.Algebra, `Complexitylib.Classes.P.Cobham.Internal.Reverse]\nlean_lib OAI where\n  roots := #[`OAI.Computability.UniqueGames.Machines.MachineBinaryParsingLemmas]\nlean_lib JointCodec where\n  roots := #[`LocalThreeSATBinaryCodec, `LocalThreeSATBinaryCodecSemantics, `LocalThreeSATBinaryCodecRuntime, `LocalThreeSATBinaryCodecUpstream]\n'
 (project/'lakefile.lean').write_bytes(config.encode());(project/'lean-toolchain').write_bytes(b'leanprover/lean4:v4.34.1\n')
 for row in rows:assert sha((OUT/row['file']).read_bytes())==row['sha256']
 assert all(not p.name.endswith(('.olean','.ilean')) for p in project.rglob('*'))
 m=dict(schema='joint-codec-minimal-source-closure-v2',source_only=True,compiler_invoked=False,local_Lean_or_Lake_invoked=False,accepted=False,compiler_admission=False,closure_complete_for_custom_OAI_and_complexitylib=True,external_import_modules=sorted(external),external_package_resolution_and_Lean4341_mathlib_d13_compatibility_unverified=True,custom_module_count=4,OAI_module_count=20,complexitylib_module_count=sum(r['kind']=='actual pinned complexitylib source' for r in rows),sources=rows,original_config_snapshots=configs,complexitylib_git_tree=dict(file='complexitylib-git-tree.json',bytes=len(tree_raw),sha256=sha(tree_raw),primary_url='https://api.github.com/repos/SamuelSchlesinger/complexitylib/git/trees/'+REV+'?recursive=1'),checks_sha256=sha(checks),selected_Lean='leanprover/lean4:v4.34.1',selected_mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',selected_complexitylib_revision=REV,selected_OAI_revision=UPREV,old_oleans_present=False,new_VM_or_disk_resources=False,Full120_scope_changed=False,config_only_new_selection=True,source_bodies_changed=False,future_native_execution_sequential_after_Full120_under_original_lease_and_admission=True)
 (OUT/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(dict(directory=str(OUT),custom=4,OAI=20,complexitylib=m['complexitylib_module_count'],bytes=sum(r['bytes'] for r in rows),manifest_sha256=sha((OUT/'manifest.json').read_bytes()),external_import_modules=sorted(external),compiler_invoked=False)),flush=True)
if __name__=='__main__':main()
