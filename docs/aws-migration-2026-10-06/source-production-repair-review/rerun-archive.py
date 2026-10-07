import hashlib,json,os,subprocess,time
from datetime import datetime,timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
CODE=REPO/'scripts/aws-archive-migration/source-retirement'
PYTHON='C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe'
env={**os.environ,'TEMP':str(REPO/'tmp/spr'),'TMP':str(REPO/'tmp/spr'),'PYTHONDONTWRITEBYTECODE':'1','GIT_CONFIG_COUNT':'1','GIT_CONFIG_KEY_0':'core.longpaths','GIT_CONFIG_VALUE_0':'true','GIT_OPTIONAL_LOCKS':'0','AWS_EC2_METADATA_DISABLED':'true'}
result={'wrapper_correction':'Import SSL before replacing socket.socket; old TypeError logs preserved. No suite assertion/code changes.','results':[]}
for name in ['test_safety.py','test_transport.py','test_endpoints.py','test_production.py']:
    print('START '+name,flush=True);timer=time.monotonic();started=datetime.now(timezone.utc).isoformat()
    wrapper="import runpy,socket,ssl; socket.socket=lambda *a,**k: (_ for _ in ()).throw(AssertionError('REVIEW_REAL_SOCKET_FORBIDDEN')); runpy.run_path("+repr(str(CODE/name))+",run_name='__main__')"
    command=[PYTHON,'-B','-c',wrapper]
    log=HERE/('archive-'+name.removesuffix('.py')+'-rerun.log')
    with log.open('xb') as out:r=subprocess.run(command,cwd=REPO,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=1500)
    result['results'].append({'name':name,'command':command,'started_at':started,'completed_at':datetime.now(timezone.utc).isoformat(),'seconds':round(time.monotonic()-timer,3),'exit_code':r.returncode,'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()})
    (HERE/'archive-rerun-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('END '+name+' exit='+str(r.returncode),flush=True)
