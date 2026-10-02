import pathlib,json,hashlib,re,os,subprocess,time
repo=pathlib.Path(__file__).resolve().parents[4]
b=repo/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
out=b/'local-native-123542';src=out/'src';lib=out/'lib';out.mkdir(exist_ok=True);log=out/'attempt-294-A7EnergyDC25';log.mkdir(exist_ok=True)
pins=json.loads((b/'local-a18-294-pins.json').read_text())
snaps={hashlib.sha256(p.read_bytes()).hexdigest().upper():p for p in (b/'source-snapshots').glob('*.snapshot')}
for s,h in pins.items():
 p=snaps.get(h.upper(),repo/s);data=p.read_bytes();assert hashlib.sha256(data).hexdigest().upper()==h
 q=src/pathlib.Path(s).relative_to('lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data)
cached=repo/'.lake/build/lib/lean'
linked=0
for file in cached.rglob('*'):
 if file.is_file():
  dest=lib/file.relative_to(cached)
  if not dest.exists():dest.parent.mkdir(parents=True,exist_ok=True);os.link(file,dest);linked+=1
(log/'cached-companions.json').write_text(json.dumps({'linked_existing_cache_files':linked,'no_download':True,'compiled_outputs_preserved':True},indent=2)+'\n')
paths=[lib,repo/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (repo/'.lake/packages').iterdir() if (p/'.lake/build/lib/lean').exists()]
env=os.environ.copy();env['LEAN_PATH']=';'.join(str(p.resolve()) for p in paths)
seen=set();failed=set();records=[]
def build(n):
 if n in seen:return n not in failed
 seen.add(n);rel=pathlib.Path(*n.split('.'));p=src/rel.with_suffix('.lean')
 if not p.exists():return True
 if n not in targets and any((base/rel.with_suffix('.olean')).exists() for base in paths):return True
 text=p.read_text(encoding='utf-8');text=re.sub(r'/\-.*?\-/','',text,flags=re.S);text=re.sub(r'--[^\n]*','',text)
 for imp in re.findall(r'^\s*(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',text,re.M):
  if not build(imp):failed.add(n);return False
 o=lib/rel.with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True);idx=len(records)
 with (log/f'stage-{idx}.stdout').open('wb') as stdout,(log/f'stage-{idx}.stderr').open('wb') as stderr:
  (log/f'stage-{idx}.lean.snapshot').write_bytes(p.read_bytes());started=time.time();r=subprocess.run([str(pathlib.Path(os.environ['USERPROFILE'])/'.elan/bin/lean.exe'),'-R',str(src),str(p),'-o',str(o)],cwd=repo,env=env,stdout=stdout,stderr=stderr,timeout=900)
 records.append({'module':n,'exit':r.returncode,'seconds':round(time.time()-started,2),'source_sha':hashlib.sha256(p.read_bytes()).hexdigest().upper()});(log/'stages.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records[-1]),flush=True)
 if r.returncode:failed.add(n)
 return r.returncode==0
targets=['PvNP.RealizableHardness.'+n+s for n in ['ActualBinaryMatrixHC46A7EnergyConsumer'] for s in ['', 'Checks']]
okay=True
for i in range(0,len(targets),2):
 good=build(targets[i]);good=build(targets[i+1]) if good else False;okay=okay and good
(log/'aggregate-exit').write_text('0' if okay else '1');raise SystemExit(0 if okay else 1)
