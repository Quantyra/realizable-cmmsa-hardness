import pathlib,json,hashlib,os,subprocess,time
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
log=b/'local-native-own374/attempt-374-DR6IncidenceChecks';log.mkdir(parents=True,exist_ok=True)
prior=b/'local-native-own372/attempt-372-DR6Incidence'
manifest=json.loads((prior/'cached-import-identities.json').read_text())
for name,h in manifest['objects'].items():assert hashlib.sha256(pathlib.Path(name).read_bytes()).hexdigest()==h
sources=json.loads((prior/'resolved-input-custody.json').read_text())
for x in sources:assert hashlib.sha256(pathlib.Path(x['exact_custody_path']).read_bytes()).hexdigest().upper()==x['sha256'].upper()
main=b/'local-native-own372/lib/PvNP/RealizableHardness/ActualBinaryMatrixHC46DR6Incidence.olean'
assert hashlib.sha256(main.read_bytes()).hexdigest().upper()=='C0D27E7C70273141243F1F7575C9A4A997B471C460EBA0ABCDAEB59CF7E8FD8A'
paths=[b/'local-native-own372/lib',b/'local-native-own371/lib',repo/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (repo/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').exists()]
env=os.environ.copy();env['LEAN_PATH']=';'.join(str(p.resolve()) for p in paths)
p=log/'stage-0.lean.snapshot';data=(b/'source-snapshots/83DF31A1CF2967A11C676D59537AA594F38BA6713EC01E76DBC33BD56D1CFB62.snapshot').read_bytes();assert hashlib.sha256(data).hexdigest().upper()=='83DF31A1CF2967A11C676D59537AA594F38BA6713EC01E76DBC33BD56D1CFB62';p.write_bytes(data)
cmd=[str(pathlib.Path(os.environ['USERPROFILE'])/'.elan/bin/lean.exe'),str(p),'-o',str(log/'ActualBinaryMatrixHC46DR6IncidenceChecks.olean')]
(log/'reused-input-identities.json').write_text(json.dumps({'Checks_only':True,'Main_rebuilt':False,'Main_source_sha256':'31305E6B9DA54B27F2B56CFD66AF6579B3179F7AE1CCACB6F197B9F0A6892ED8','Main_object_sha256':hashlib.sha256(main.read_bytes()).hexdigest().upper(),'LEAN_PATH':env['LEAN_PATH'],'invocation':cmd,'cached_manifest':str(prior/'cached-import-identities.json'),'source_custody':str(prior/'resolved-input-custody.json'),'verified_object_count':len(manifest['objects']),'verified_source_count':len(sources),'development_only':True,'full_source_debt':True},indent=2)+'\n')
started=time.time()
with (log/'stage-0.stdout').open('wb') as out,(log/'stage-0.stderr').open('wb') as err:r=subprocess.run(cmd,cwd=repo,env=env,stdout=out,stderr=err)
t={'exit_code':r.returncode,'seconds':round(time.time()-started,2),'Checks_only':True,'Main_rebuilt':False};(log/'terminal.json').write_text(json.dumps(t,indent=2)+'\n');print(json.dumps(t),flush=True);raise SystemExit(r.returncode)
