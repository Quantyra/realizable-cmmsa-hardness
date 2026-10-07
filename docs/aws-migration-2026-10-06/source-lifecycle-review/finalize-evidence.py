"""Hash retained synthetic fixtures and audit files; record final read-only source status."""
import hashlib
import json
from pathlib import Path
import subprocess
from datetime import datetime,timezone
AUDIT=Path(__file__).resolve().parent
REPO=AUDIT.parents[2]
WEBSITE=REPO.parent/'Quantyra-Website'
PARENT=REPO.parent/'IGH/Quantyra-Planning'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
paths=[]
for p in sorted((AUDIT/'synthetic-temp').rglob('*')):
    if p.is_file() and '.git' not in p.parts:paths.append(pin(p))
special=json.loads((AUDIT/'independent-archive-recreated-results.json').read_bytes())
fixture=Path(special['fixture'])
for p in sorted(fixture.rglob('*')):
    if p.is_file() and '.git' not in p.parts:paths.append(pin(p))
(AUDIT/'fixture-hashes.json').write_text(json.dumps({'type':'synthetic-only-retained-fixture-index',
    'real_cloud_requests':0,'real_mutations':0,'fixtures':paths},indent=2),encoding='utf-8')
files=[pin(p) for p in sorted(AUDIT.iterdir()) if p.is_file() and p.name!='evidence-index.json']
statuses={str(p):subprocess.check_output(['git','status','--porcelain=v1'],cwd=p,text=True) for p in (REPO,WEBSITE,PARENT)}
source=json.loads((AUDIT/'before.json').read_bytes())
same={}
for name,repo in [('archive',REPO),('website',WEBSITE)]:
    same[name]=all(sha(repo/relative)==h for relative,h in source[name]['files'].items())
assert all(same.values())
reports=[PARENT/'docs/aws-migration-2026-10-06'/n for n in ('source-lifecycle-production-independent-review.md','source-lifecycle-production-review-cli-final.md')]
index={'type':'source-lifecycle-independent-production-review-evidence-v1','finalized_at':datetime.now(timezone.utc).isoformat(),
       'code_verdict':{'archive':'NO-GO','website':'NO-GO'},'live_eligibility':'HOLD',
       'reviewed_commits':{'archive':'12a58220884586e42149acc6844821b64ff07536','website':'39c629bc151f734d07c64330c13f64a84d9e104c'},
       'reviewed_source_unchanged':same,'real_cloud_requests':0,'real_mutations':0,
       'original_payload_key_secret_retrievals':0,'source_repository_git_writes':0,
       'prescribed_final_tests':{'archive':68,'website':26,'passed':94},'additional_independent_checks':15,
       'statuses':statuses,'audit_files':files,'parent_reports':[pin(p) for p in reports if p.is_file()]}
(AUDIT/'evidence-index.json').write_text(json.dumps(index,indent=2),encoding='utf-8')
print(json.dumps({'files':len(files),'fixture_files':len(paths),'source_unchanged':same,'reports':len(index['parent_reports'])}))
