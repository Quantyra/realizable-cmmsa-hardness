"""Independent local review; cloud sockets forbidden, no production Git writes."""
import hashlib, json, os, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path
HERE = Path(__file__).resolve().parent
REPO = next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
WEB = REPO.parent/'Quantyra-Website'
CODE = REPO/'scripts/aws-archive-migration/source-retirement'
PYTHON = Path('C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe')
TEMP = REPO/'tmp/spr'
TEMP.mkdir(parents=True, exist_ok=True)
def now(): return datetime.now(timezone.utc).isoformat()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(repo, *args):
    return subprocess.check_output(['git', '-c', 'core.fsmonitor=false', *args], cwd=repo, env={**os.environ, 'GIT_OPTIONAL_LOCKS':'0'}).decode().strip()
def snapshot():
    result={}
    for repo, scope in [(REPO,'scripts/aws-archive-migration/source-retirement'),(WEB,'scripts/aws-migration')]:
        files=git(repo,'ls-files',scope).splitlines()
        result[str(repo)]={'head':git(repo,'rev-parse','HEAD'),'status':git(repo,'status','--short'),
            'files':{n:sha(repo/n) for n in files if 'node_modules/' not in n}}
    return result
before=snapshot()
(HERE/'before.json').write_text(json.dumps(before,indent=2)+'\n')
env={**os.environ,'TEMP':str(TEMP),'TMP':str(TEMP),'PYTHONDONTWRITEBYTECODE':'1',
     'GIT_CONFIG_COUNT':'1','GIT_CONFIG_KEY_0':'core.longpaths','GIT_CONFIG_VALUE_0':'true',
     'GIT_OPTIONAL_LOCKS':'0','AWS_EC2_METADATA_DISABLED':'true'}
record={'started_at':now(),'real_cloud_requests':0,'production_mutations':0,'production_git_writes':0,'source_eligibility':'HOLD','results':[]}
def run(name, args, cwd=REPO):
    print('START '+name,flush=True);start=now();timer=time.monotonic()
    with (HERE/(name+'.log')).open('xb') as out:
        r=subprocess.run(args,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=1500)
    row={'name':name,'command':list(map(str,args)),'cwd':str(cwd),'started_at':start,'completed_at':now(),
         'seconds':round(time.monotonic()-timer,3),'exit_code':r.returncode,'log_sha256':sha(HERE/(name+'.log'))}
    record['results'].append(row)
    (HERE/'prescribed-results.json').write_text(json.dumps(record,indent=2)+'\n')
    print('END '+name+' exit='+str(r.returncode),flush=True)
for name in ['test_safety.py','test_transport.py','test_endpoints.py','test_production.py']:
    wrapper="import runpy,socket; socket.socket=lambda *a,**k: (_ for _ in ()).throw(AssertionError('REVIEW_REAL_SOCKET_FORBIDDEN')); runpy.run_path("+repr(str(CODE/name))+",run_name='__main__')"
    run('archive-'+name.removesuffix('.py'),[str(PYTHON),'-B','-c',wrapper])
for name in ['independent-archive-repaired-final4.py','independent-archive-recreated-repaired-final4.py']:
    source=(CODE/'evidence/production-repair'/name).read_text()
    source=source.replace("Path('Q:/fixtures')",repr(TEMP).replace('WindowsPath','Path'))
    target=HERE/name
    target.write_text(source,encoding='utf-8')
    run('adapted-'+name.removesuffix('.py'),[str(PYTHON),'-B',str(target)])
run('archive-original305-binder',['node',str(CODE/'bind-proof.mjs'),'--verify-only'])
run('archive-default',[str(PYTHON),'-B',str(CODE/'cli.py')])
preload=HERE/'deny-network.cjs'
preload.write_text("const forbid=()=>{throw Error('REVIEW_REAL_NETWORK_FORBIDDEN')}; for(const m of ['net','tls']){const x=require('node:'+m);x.connect=forbid;x.createConnection=forbid;} for(const m of ['http','https']){const x=require('node:'+m);x.request=forbid;x.get=forbid;} globalThis.fetch=forbid;\n")
run('website-lifecycle',['node','--require',str(preload),'--test','scripts/aws-migration/source-lifecycle/safety.test.mjs','scripts/aws-migration/source-lifecycle/integration.test.mjs','scripts/aws-migration/source-lifecycle/repair.test.mjs'],WEB)
run('website-migration',['node','--require',str(preload),'--test','scripts/aws-migration/test.mjs','scripts/aws-migration/route53.test.mjs','scripts/aws-migration/bucket-policy.test.mjs'],WEB)
run('website-default',['node','--require',str(preload),'scripts/aws-migration/source-lifecycle/lifecycle.mjs'],WEB)
run('website-dns-default',['node','--require',str(preload),'scripts/aws-migration/source-lifecycle/dns-cleanup.mjs'],WEB)
after=snapshot()
(HERE/'after-prescribed.json').write_text(json.dumps(after,indent=2)+'\n')
record.update(completed_at=now(),owned_tracked_bytes_unchanged=all(before[k]['files']==after[k]['files'] for k in before),
              production_heads_unchanged=all(before[k]['head']==after[k]['head'] for k in before))
(HERE/'prescribed-results.json').write_text(json.dumps(record,indent=2)+'\n')
print('FINISHED '+str(all(r['exit_code']==0 for r in record['results'])),flush=True)
