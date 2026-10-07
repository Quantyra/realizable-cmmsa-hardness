"""Validate local committed artifact identities and retain bounded audit metadata only."""
from datetime import datetime,timezone
import hashlib
import inspect
import json
from pathlib import Path
import subprocess
import sys
AUDIT=Path(__file__).resolve().parent
ARCHIVE=AUDIT.parents[2]
WEBSITE=ARCHIVE.parent/'Quantyra-Website'
PARENT=ARCHIVE.parent/'IGH/Quantyra-Planning'
def sha(b):return hashlib.sha256(b).hexdigest()
def read_json(p):return json.loads(p.read_bytes())
results={'observed_at':datetime.now(timezone.utc).isoformat(),'real_cloud_requests':0,'real_mutations':0}
for name,repo,scope,commit in [
    ('archive',ARCHIVE,'scripts/aws-archive-migration/source-retirement','12a58220884586e42149acc6844821b64ff07536'),
    ('website',WEBSITE,'scripts/aws-migration/source-lifecycle','39c629bc151f734d07c64330c13f64a84d9e104c')]:
    files={str(p.relative_to(repo)).replace('\\','/'):sha(p.read_bytes()) for p in sorted((repo/scope).rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
    checks=[]
    for relative,h in files.items():
        b=subprocess.check_output(['git','show',commit+':'+relative],cwd=repo)
        checks.append({'path':relative,'sha256':h,'matches_reviewed_commit':sha(b)==h})
    assert all(x['matches_reviewed_commit'] for x in checks)
    results[name]={'reviewed_commit':commit,'current_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'files':checks}
here=ARCHIVE/'scripts/aws-archive-migration/source-retirement'
manifest=read_json(here/'evidence/completion-artifact-hashes.json')
checks=[]
for row in manifest['artifacts']:
    b=(here/row['path']).read_bytes()
    checks.append({'path':row['path'],'sha256':sha(b),'pass':len(b)==row['bytes'] and sha(b)==row['sha256']})
assert all(r['pass'] for r in checks)
results['archive_completion_manifest']={'sha256':sha((here/'evidence/completion-artifact-hashes.json').read_bytes()),'count':len(checks),'checks':checks}
website_evidence=WEBSITE/'evidence/source-lifecycle-completion-2026-10-07'
index=read_json(website_evidence/'completion-verification.json')
checks=[{'path':p,'sha256':sha((website_evidence/p).read_bytes()),'pass':sha((website_evidence/p).read_bytes())==h} for p,h in index['artifacts'].items()]
assert all(r['pass'] for r in checks)
results['website_completion_manifest']={'sha256':sha((website_evidence/'completion-verification.json').read_bytes()),'count':len(checks),'checks':checks,'historical_preflight':index['preflight'],'toolingHash':index['toolingHash']}
import boto3,botocore
from botocore.endpoint import Endpoint
from botocore.httpsession import URLLib3Session
old=read_json(here/'evidence/completion-sdk-inspection.json')
sdk={'boto3':boto3.__version__,'botocore':botocore.__version__,'python':sys.version,
     'endpoint_send_request_sha256':sha(inspect.getsource(Endpoint._send_request).encode()),
     'http_send_sha256':sha(inspect.getsource(URLLib3Session.send).encode()),
     'http_disables_urllib3_retries':'retries=Retry(False)' in inspect.getsource(URLLib3Session.send)}
sdk['matches_author_inspection']=all(sdk[k]==old[k] for k in ('boto3','botocore','endpoint_send_request_sha256','http_send_sha256'))
assert sdk['matches_author_inspection'] and sdk['http_disables_urllib3_retries']
results['installed_python_sdk']=sdk
node_handler=WEBSITE/'scripts/aws-migration/node_modules/@smithy/node-http-handler/dist-cjs/index.js'
results['installed_node_http_handler']={'path':str(node_handler),'sha256':sha(node_handler.read_bytes())}
context=[PARENT/'docs/aws-migration-2026-10-06'/n for n in (
    'source-lifecycle-production-review-dispatch.txt','status.md','archive-source-retirement-completion-result.md',
    'website-source-lifecycle-completion-result.md','archive-recovery-hardlink-repair-result.md')]
results['parent_context']=[{'path':str(p),'sha256':sha(p.read_bytes())} for p in context]
results['statuses']={str(p):subprocess.check_output(['git','status','--porcelain=v1'],cwd=p,text=True) for p in (ARCHIVE,WEBSITE,PARENT)}
(AUDIT/'evidence-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
print(json.dumps({'archive_scoped_files':len(results['archive']['files']),'website_scoped_files':len(results['website']['files']),
                  'archive_artifact_pins':len(results['archive_completion_manifest']['checks']),
                  'website_receipt_pins':len(checks),'sdk_source_matches':sdk['matches_author_inspection'],
                  'reviewed_scoped_bytes_match_commits':True}))
