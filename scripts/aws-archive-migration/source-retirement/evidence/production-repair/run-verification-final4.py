"""Sequential, immutable local repair verification receipts; no AWS factory used."""
import hashlib,json,os,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
CODE=REPO/'scripts/aws-archive-migration/source-retirement'
sys.path.insert(0,str(CODE))
from root import pins
import boto3,botocore,botocore.args,botocore.httpsession,ssl
fixture=Path('Q:/');fixture.mkdir(exist_ok=True)
env=os.environ.copy();env.update(TEMP=str(fixture),TMP=str(fixture),PYTHONDONTWRITEBYTECODE='1',GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='core.longpaths',GIT_CONFIG_VALUE_0='true')
def now():return datetime.now(timezone.utc).isoformat()
before=pins()
runtime={str(p):hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in (sys.executable,botocore.args.__file__,botocore.httpsession.__file__,Path(sys.executable).parent/'python313.zip')}
record={'started_at':now(),'code_sha256':before,'runtime_sha256':runtime,'boto3':boto3.__version__,'botocore':botocore.__version__,'python':sys.version,'real_cloud_requests':0,'real_mutations':0,'eligibility':'HOLD','results':[]}
commands=[('safety',[sys.executable,'-B',str(CODE/'test_safety.py')]),('transport',[sys.executable,'-B',str(CODE/'test_transport.py')]),('endpoints',[sys.executable,'-B',str(CODE/'test_endpoints.py')]),('production',[sys.executable,'-B',str(CODE/'test_production.py')]),('independent-endpoint',[sys.executable,'-B',str(HERE/'independent-archive-repaired-final4.py')]),('independent-replacement',[sys.executable,'-B',str(HERE/'independent-archive-recreated-repaired-final4.py')]),('original305-binder',['node',str(CODE/'bind-proof.mjs'),'--verify-only']),('offline-default',[sys.executable,'-B',str(CODE/'cli.py')])]
# Only the synthetic test directory naming changed. Require byte-identical
# implementation and all unchanged test files before reusing passing suites.
previous=json.loads((HERE/'final3-verification.json').read_text())
assert all(sha==before[name] for name,sha in previous['code_sha256'].items() if name!='test_production.py')
reuse={'safety','transport','endpoints'}
record['reused_suite_basis']='All implementation files and reused suite files byte-identical; only test_production synthetic directory names shortened. Complete production suite and independent probes rerun on final bytes.'
record['results']=[{**r,'reused_unchanged_suite':True,'log':r['name']+'-final3.log'} for r in previous['results'] if r['name'] in reuse]
assert all(r['exit_code']==0 for r in record['results'])
commands=[(n,c) for n,c in commands if n not in reuse]
for name,command in commands:
    print('START',name,flush=True);started=now();timer=time.monotonic()
    with (HERE/(name+'-final4.log')).open('xb') as f:
        r=subprocess.run(command,cwd=REPO,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=1200)
    row={'name':name,'command':command,'started_at':started,'completed_at':now(),'seconds':time.monotonic()-timer,'exit_code':r.returncode}
    record['results'].append(row);print('END',name,'exit',r.returncode,flush=True)
    assert pins()==before,'CODE_CHANGED_DURING_SUITES'
record.update(completed_at=now(),code_after=pins())
with (HERE/'final4-verification.json').open('x') as f:json.dump(record,f,indent=2)
print('FINISHED',all(r['exit_code']==0 for r in record['results']),flush=True)
