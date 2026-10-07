"""Independent, sequential local verification. No real AWS calls or repository Git writes."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
from datetime import datetime, timezone

AUDIT = Path(__file__).resolve().parent
ARCHIVE = AUDIT.parents[2]
WEBSITE = ARCHIVE.parent / 'Quantyra-Website'
PYTHON = Path('C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe')
NODE = Path('C:/Program Files/nodejs/node.exe')

def utc():
    return datetime.now(timezone.utc).isoformat()

def snapshot():
    result = {}
    for name, repo, source in [('archive', ARCHIVE, 'scripts/aws-archive-migration/source-retirement'),
                               ('website', WEBSITE, 'scripts/aws-migration/source-lifecycle')]:
        result[name] = {
            'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
            'status': subprocess.check_output(['git', 'status', '--porcelain=v1'], cwd=repo, text=True),
            'files': {str(p.relative_to(repo)).replace('\\', '/'): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted((repo/source).rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
        }
    return result

env = os.environ.copy()
env['PYTHONDONTWRITEBYTECODE'] = '1'
env['AWS_EC2_METADATA_DISABLED'] = 'true'
temp = AUDIT / 'synthetic-temp'
temp.mkdir(exist_ok=True)
env['TEMP'] = env['TMP'] = str(temp)
before = snapshot()
(AUDIT/'before.json').write_text(json.dumps(before, indent=2), encoding='utf-8')
prefix = 'scripts/aws-archive-migration/source-retirement/'
suites = [
    ('archive-default-check', ARCHIVE, [str(PYTHON), '-B', prefix+'cli.py']),
    ('archive-safety', ARCHIVE, [str(PYTHON), '-B', prefix+'test_safety.py']),
    ('archive-transport', ARCHIVE, [str(PYTHON), '-B', prefix+'test_transport.py']),
    ('archive-production', ARCHIVE, [str(PYTHON), '-B', prefix+'test_production.py']),
    ('archive-original-proof-binder', ARCHIVE, [str(NODE), prefix+'bind-proof.mjs', '--verify-only']),
    ('website-default-check', WEBSITE, [str(NODE), 'scripts/aws-migration/source-lifecycle/lifecycle.mjs']),
    ('website-safety-and-integration', WEBSITE, [str(NODE), '--test', 'scripts/aws-migration/source-lifecycle/safety.test.mjs', 'scripts/aws-migration/source-lifecycle/integration.test.mjs']),
]
results = []
for name, repo, command in suites:
    print('START '+name+' '+utc(), flush=True)
    current = snapshot()
    if any(current[k]['files'] != before[k]['files'] for k in before):
        raise RuntimeError('Reviewed source bytes changed during verification')
    log = AUDIT / (name+'.log')
    started = utc()
    with log.open('wb') as output:
        run = subprocess.run(command, cwd=repo, env=env, stdout=output, stderr=subprocess.STDOUT)
    result = {'name': name, 'cwd': str(repo), 'command': command, 'started': started,
              'finished': utc(), 'exit_code': run.returncode, 'log': str(log),
              'sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
    results.append(result)
    (AUDIT/'prescribed-results.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
    print('FINISH '+name+' exit='+str(run.returncode)+' '+utc(), flush=True)
after = snapshot()
(AUDIT/'after-prescribed.json').write_text(json.dumps(after, indent=2), encoding='utf-8')
assert all(after[k]['files'] == before[k]['files'] for k in before)
print(json.dumps({'suites': len(results), 'all_passed': all(r['exit_code']==0 for r in results),
                  'reviewed_source_unchanged': True}), flush=True)
