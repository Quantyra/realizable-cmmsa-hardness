import hashlib,json,os,subprocess
from datetime import datetime,timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
WEB=REPO.parent/'Quantyra-Website'
PARENT=REPO.parent/'IGH/Quantyra-Planning'
env={**os.environ,'GIT_OPTIONAL_LOCKS':'0'}
def git(repo,*args):return subprocess.check_output(['git',*args],cwd=repo,env=env).decode().strip()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
before=json.loads((HERE/'before.json').read_bytes())
final={};unchanged={}
for name,prior in before.items():
    repo=Path(name);current={n:sha(repo/n) for n in prior['files']}
    final[name]={'head':git(repo,'rev-parse','HEAD'),'status':git(repo,'status','--short'),'files':current}
    unchanged[name]={'head':final[name]['head']==prior['head'],'tracked_files':current==prior['files']}
assert all(all(x.values()) for x in unchanged.values())
(HERE/'after-final.json').write_text(json.dumps(final,indent=2)+'\n')
reports=[PARENT/'docs/aws-migration-2026-10-06/source-production-repair-independent-review.md',PARENT/'docs/aws-migration-2026-10-06/source-production-repair-review-cli-final.md']
audit=[pin(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='evidence-index.json']
fixtures=[]
for p in sorted((REPO/'tmp/spr').rglob('*')):
    if p.is_file() and '.git' not in p.parts and p.suffix in ['.json','.jsonl','.journal']:
        fixtures.append(pin(p))
(HERE/'fixture-hashes.json').write_text(json.dumps({'type':'retained-local-synthetic-review-fixtures','files':fixtures},indent=2)+'\n')
audit.append(pin(HERE/'fixture-hashes.json'))
record={'type':'source-production-repair-independent-review-evidence-v1','finalized_at':datetime.now(timezone.utc).isoformat(),
        'reviewed_commits':{'archive':final[str(REPO)]['head'],'website':final[str(WEB)]['head']},
        'code_verdict':{'archive':'GO-with-documented-operating-boundaries','website':'NO-GO'},'live_eligibility':'HOLD',
        'remaining_findings':['R1-successful-204-freeze-transition-rejected','R2-incomplete-related-ACM-inventory'],
        'unchanged':unchanged,'real_cloud_requests':0,'real_cloud_mutations':0,'production_code_writes':0,'production_git_writes':0,
        'real_credentials_keys_remote_payload_secret_reads':0,'scientific_execution':0,'prescribed_tests':131,'independent_scenarios':22,
        'tests':{'archive_safety':45,'archive_transport':2,'archive_endpoints':2,'archive_production':26,'website_lifecycle':40,'website_migration_regression':16},
        'statuses':{str(repo):git(repo,'status','--short') for repo in [REPO,WEB,PARENT]},
        'reports':[pin(p) for p in reports],'audit_files':audit,'synthetic_fixture_metadata_pins':len(fixtures),
        'runtime':{'node':subprocess.check_output(['node','--version']).decode().strip(),'python_executable':'C:/Users/dfred/QuantyraTools/SpaceProofs/python/python.exe','boto3_botocore':'1.43.108','website_AWS_SDK':'3.1147.0'},
        'limits':['Past owner service receipts verified locally; no fresh cloud state observed.','All real gates/retirement overlay remain disabled.','Report and evidence intentionally uncommitted; no complete migration certification.']}
(HERE/'evidence-index.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'verdict':record['code_verdict'],'eligibility':record['live_eligibility'],'unchanged':unchanged,'audit_files':len(audit),'retained_fixture_metadata_files':len(fixtures),'runtime':record['runtime'],'reports':record['reports']},indent=2))
