import pathlib,json,hashlib,os,subprocess,time
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
log=b/'local-native-own375/attempt-375-DR6Moment';log.mkdir(parents=True,exist_ok=True)
prior=b/'local-native-own372/attempt-372-DR6Incidence'
manifest=json.loads((prior/'cached-import-identities.json').read_text())
for name,h in manifest['objects'].items():assert hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()==h
sources=json.loads((prior/'resolved-input-custody.json').read_text())
for x in sources:assert hashlib.sha256(pathlib.Path(x['exact_custody_path']).read_bytes()).hexdigest().upper()==x['sha256'].upper()
main=b/'local-native-own372/lib/PvNP/RealizableHardness/ActualBinaryMatrixHC46DR6Incidence.olean'
assert hashlib.sha256(main.read_bytes()).hexdigest().upper()=='C0D27E7C70273141243F1F7575C9A4A997B471C460EBA0ABCDAEB59CF7E8FD8A'
overlay=b/'local-native-own375/lib';overlay.mkdir(parents=True,exist_ok=True)
linked={}
for file in (b/'local-native-own372/lib/PvNP').rglob('*'):
 if file.is_file() and 'ActualBinaryMatrixHC46DR6Moment' not in file.name:
  dest=overlay/file.relative_to(b/'local-native-own372/lib');dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():os.link(file,dest)
  linked[str(dest)]=hashlib.sha256(dest.read_bytes()).hexdigest()
paths=[overlay,b/'local-native-own372/lib',b/'local-native-own371/lib',repo/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (repo/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').exists()]
env=os.environ.copy();env['LEAN_PATH']=';'.join(str(p.resolve()) for p in paths)
(log/'reused-input-identities.json').write_text(json.dumps({'Main_Incidence_rebuilt':False,'Incidence_object_sha256':hashlib.sha256(main.read_bytes()).hexdigest().upper(),'LEAN_PATH':env['LEAN_PATH'],'cached_manifest':str(prior/'cached-import-identities.json'),'source_custody':str(prior/'resolved-input-custody.json'),'verified_object_count':len(manifest['objects']),'verified_source_count':len(sources),'overlay_objects':linked,'development_only':True,'full_source_debt':True},indent=2)+'\n')
records=[];okay=True
for idx,(name,h) in enumerate([('ActualBinaryMatrixHC46DR6Moment','68DE9B61FB3AAC19F2776B111CB4E500E7594F7D45B46A5D6F330E5B55690291'),('ActualBinaryMatrixHC46DR6MomentChecks','3C1055736AB36A53BBD325F72F2570ED5ED4CF30DC9E6CF3B8768B8032E4B737')]):
 data=(b/'source-snapshots'/(h+'.snapshot')).read_bytes();assert hashlib.sha256(data).hexdigest().upper()==h
 p=log/('stage-'+str(idx)+'.lean.snapshot');p.write_bytes(data);obj=overlay/'PvNP/RealizableHardness'/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(pathlib.Path(os.environ['USERPROFILE'])/'.elan/bin/lean.exe'),str(p),'-o',str(obj)];started=time.time()
 with (log/('stage-'+str(idx)+'.stdout')).open('wb') as out,(log/('stage-'+str(idx)+'.stderr')).open('wb') as err:r=subprocess.run(cmd,cwd=repo,env=env,stdout=out,stderr=err)
 rec={'module':name,'exit_code':r.returncode,'seconds':round(time.time()-started,2),'source_sha256':h,'invocation':cmd}
 if r.returncode==0:rec['object_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest().upper()
 records.append(rec);(log/'stages.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(rec),flush=True)
 if r.returncode:okay=False;break
terminal={'exit_code':0 if okay else 1,'Incidence_rebuilt':False};(log/'terminal.json').write_text(json.dumps(terminal,indent=2)+'\n');raise SystemExit(terminal['exit_code'])
