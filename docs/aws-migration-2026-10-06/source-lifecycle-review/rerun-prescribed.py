"""Repeat failed suites with a short fixture path outside the historical evidence name."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
from datetime import datetime, timezone
AUDIT = Path(__file__).resolve().parent
REPO = AUDIT.parents[2]
WEBSITE = REPO.parent/'Quantyra-Website'
env = os.environ.copy()
env['PYTHONDONTWRITEBYTECODE'] = '1'
env['AWS_EC2_METADATA_DISABLED'] = 'true'
temp=REPO/'tmp/slr'
temp.mkdir(parents=True,exist_ok=True)
env['TMP']=env['TEMP']=str(temp)
# Exact committed filenames must survive Windows Git. Preserve first-run failures.
env['GIT_CONFIG_COUNT']='1'
env['GIT_CONFIG_KEY_0']='core.longpaths'
env['GIT_CONFIG_VALUE_0']='true'
results=[]
for name,cwd,command in [
    ('archive-production-rerun',REPO,['C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe','-B','scripts/aws-archive-migration/source-retirement/test_production.py']),
    ('website-safety-and-integration-rerun',WEBSITE,['C:/Program Files/nodejs/node.exe','--test','scripts/aws-migration/source-lifecycle/safety.test.mjs','scripts/aws-migration/source-lifecycle/integration.test.mjs'])]:
    started=datetime.now(timezone.utc).isoformat()
    print('START '+name+' '+started,flush=True)
    log=AUDIT/(name+'.log')
    with log.open('wb') as out:
        r=subprocess.run(command,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT)
    results.append({'name':name,'started':started,'finished':datetime.now(timezone.utc).isoformat(),
                    'cwd':str(cwd),'command':command,'exit_code':r.returncode,'log':str(log),
                    'sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
                    'fixture_temp':str(temp),'process_only_git_config':{'core.longpaths':'true'}})
    (AUDIT/'prescribed-rerun-results.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    print('FINISH '+name+' exit='+str(r.returncode),flush=True)
