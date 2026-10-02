import hashlib, json, os, subprocess, sys, tarfile, time, traceback
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'docs/native-receipts/ActualSelectedComplementAnalyticMoment/runtime-prebuild'
RUN=BASE/'local-native-own389'
ATTEMPT=RUN/'attempt-389-A7T1Transfer'
MODULE='ActualBinaryMatrixHC46A7T1Transfer'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x): Path(p).write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
def guard(p,h):
    if sha(p).lower()!=h.lower(): raise RuntimeError('identity mismatch: '+str(p))

if ATTEMPT.exists(): raise RuntimeError('attempt already exists; retain sole prior owner')
ATTEMPT.mkdir(parents=True)
stages=[]
try:
    prior_path=BASE/'local-native-own388/attempt-388-A7HybridW6Transport/reused-input-identities.json'
    prior=json.loads(prior_path.read_bytes())
    cached=json.loads(Path(prior['cached_manifest']).read_bytes())
    custody=json.loads(Path(prior['source_custody']).read_bytes())
    for p,h in cached['objects'].items(): guard(p,h)
    for item in custody: guard(item['exact_custody_path'],item['sha256'])
    for p,h in prior['overlay_objects'].items(): guard(p,h)
    prior_stages=json.loads((prior_path.parent/'stages.json').read_bytes())
    for item in prior_stages: guard(item['invocation'][-1],item['object_sha256'])
    lib=RUN/'lib'
    oldlib=BASE/'local-native-own388/lib'
    linked={}
    for old,h in prior['overlay_objects'].items():
        old=Path(old);rel=old.relative_to(oldlib)
        if rel.name.startswith(MODULE): continue
        dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        os.link(old,dest)
        linked[str(dest)]=h
    oldpaths=prior['LEAN_PATH'].split(';')
    leanpath=';'.join([str(lib)]+oldpaths)
    archive=Path(sys.argv[1]).resolve()
    with tarfile.open(archive,'r:gz') as t:
        manifest=json.loads(t.extractfile('manifest.json').read())
        source_bytes={}
        for name in [MODULE,MODULE+'Checks']:
            member=name+'.lean';b=t.extractfile(member).read()
            expected=manifest['files'][member]['sha256']
            if hashlib.sha256(b).hexdigest().lower()!=expected.lower(): raise RuntimeError('captured input mismatch')
            if b.startswith(b'\xef\xbb\xbf'): raise RuntimeError('BOM in captured source')
            text=b.decode('utf-8',errors='strict')
            if '->'+chr(0x2097)+'[' in text: raise RuntimeError('mixed ASCII linear-map arrow token')
            source_bytes[name]=b
    dump(ATTEMPT/'reused-input-identities.json',{'LEAN_PATH':leanpath,'cached_manifest':prior['cached_manifest'],'source_custody':prior['source_custody'],'verified_object_count':len(cached['objects']),'verified_source_count':len(custody),'overlay_objects':linked,'prior_stage_objects':prior_stages,'input_archive':str(archive),'input_archive_sha256':sha(archive),'development_only':True,'full_source_debt':True,'accepted_modules_rebuilt':False})
    env=dict(os.environ);env['LEAN_PATH']=leanpath
    for i,name in enumerate([MODULE,MODULE+'Checks']):
        snapshot=ATTEMPT/('stage-'+str(i)+'.lean.snapshot');snapshot.write_bytes(source_bytes[name])
        obj=lib/'PvNP/RealizableHardness'/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        if obj.exists(): raise RuntimeError('target output already exists')
        invocation=[str(Path.home()/'.elan/bin/lean.exe'),str(snapshot),'-o',str(obj)]
        start=time.monotonic()
        with (ATTEMPT/('stage-'+str(i)+'.stdout')).open('wb') as out,(ATTEMPT/('stage-'+str(i)+'.stderr')).open('wb') as err:
            process=subprocess.Popen(invocation,cwd=ROOT,env=env,stdout=out,stderr=err)
            dump(ATTEMPT/('stage-'+str(i)+'.process.json'),{'pid':process.pid,'invocation':invocation,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
            code=process.wait()
        item={'module':name,'exit_code':code,'seconds':round(time.monotonic()-start,2),'source_sha256':sha(snapshot),'invocation':invocation}
        if obj.exists(): item['object_sha256']=sha(obj)
        stages.append(item);dump(ATTEMPT/'stages.json',stages)
        if code: break
    code=stages[-1]['exit_code']
    dump(ATTEMPT/'terminal.json',{'aggregate_exit':code,'development_only':True,'full_source_debt':True,'accepted_modules_rebuilt':False})
    print(json.dumps({'attempt':str(ATTEMPT),'aggregate_exit':code,'stages':stages}))
    sys.exit(code)
except Exception:
    text=traceback.format_exc();(ATTEMPT/'infrastructure-exception.txt').write_text(text,encoding='utf-8')
    dump(ATTEMPT/'terminal.json',{'status':'infrastructure_failure','aggregate_exit':None,'accepted_modules_rebuilt':False})
    raise
