import hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
WEB=REPO.parent/'Quantyra-Website'
OWN=REPO/'scripts/aws-archive-migration/source-retirement/evidence/production-repair'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def git(repo,*args):return subprocess.check_output(['git',*args],cwd=repo,env={**os.environ,'GIT_OPTIONAL_LOCKS':'0'})
def validate(rows,key='file',root=REPO):
    result=[]
    for x in rows:
        p=Path(x[key]);p=p if p.is_absolute() else root/p
        expected=x.get('sha256',x.get('expected_sha256'))
        result.append({'file':str(p),'sha256':sha(p),'expected':expected,'matches':sha(p)==expected,
                       'bytes_match':x.get('bytes',p.stat().st_size)==p.stat().st_size})
    return {'count':len(result),'all_match':all(x['matches'] and x['bytes_match'] for x in result),'failures':[x for x in result if not x['matches'] or not x['bytes_match']]}
result={}
result['archive_manifest']=validate(read(OWN/'final-artifact-hashes-v3.json')['files'])
result['archive_manifest_sha256']=sha(OWN/'final-artifact-hashes-v3.json')
result['old_review_fixtures']=validate(read(REPO/'docs/aws-migration-2026-10-06/source-lifecycle-review/fixture-hashes.json')['fixtures'],'path')
result['new_owner_fixtures']=validate(read(OWN/'new-fixture-hashes.json')['fixtures'],'physical_path')
index=read(WEB/'evidence/source-production-repair-2026-10-07/verification-index.json')
result['website_manifest']=validate([{'file':n,**p} for n,p in index['artifacts'].items()],root=WEB/'evidence/source-production-repair-2026-10-07')
result['website_index_sha256']=sha(WEB/'evidence/source-production-repair-2026-10-07/verification-index.json')
result['website_protected_paths']=validate([{'file':n,'sha256':p} for n,p in index['preservation']['protectedTrackedHashes'].items()],root=WEB) if 'protectedTrackedHashes' in index['preservation'] else {'keys':list(index['preservation'])}
result['commits']={}
for repo,commits,scope in [(REPO,['98da0a078ec8e223a21a71801b060c0b0a148875'],['scripts/aws-archive-migration/source-retirement/']),
    (WEB,['617791bd97a4d8aafa3d452c4e9c0b1f265cbc3a','cc004fd3b2e37c9988dcb991b2b887116a5ad6e1','b73ad4f368c23a15cf2ca97d94e09787106ef62c'],['scripts/aws-migration/source-lifecycle/','scripts/aws-migration/route53.mjs','evidence/source-production-repair-2026-10-07/'])]:
    paths=git(repo,'ls-files',scope[0]).decode().splitlines()
    if repo==WEB:paths.append('scripts/aws-migration/route53.mjs')
    compared=[]
    for p in paths:
        b=git(repo,'show',commits[-1]+':'+p);raw=(repo/p).read_bytes()
        compared.append({'file':p,'raw_sha256':sha(repo/p),'git_blob_sha256':hashlib.sha256(b).hexdigest(),
                         'matches_raw_or_git_text_normalization':b in (raw,raw.replace(b'\r\n',b'\n'))})
    rows=[]
    for commit in commits:
        changed=git(repo,'diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines()
        rows.append({'commit':commit,'changed_count':len(changed),'all_in_owner_scope':all(any(p.startswith(s) for s in scope) for p in changed)})
    result['commits'][str(repo)]={'head':git(repo,'rev-parse','HEAD').decode().strip(),'commits':rows,'files':compared,'all_match':all(x['matches_raw_or_git_text_normalization'] for x in compared)}
fixtures=[]
for name in ['disposable-service-fixture.json','disposable-service-fixture-recovery.json','disposable-service-fixture-rerun.json','disposable-service-fixture-final.json']:
    d=read(WEB/'evidence/source-production-repair-2026-10-07'/name)
    ops=d.get('operations',[])
    fixtures.append({'file':name,'sha256':sha(WEB/'evidence/source-production-repair-2026-10-07'/name),'bucket':d.get('bucket'),'identity':d.get('identity'),
       'body_sha256':d.get('bodySHA256'),'fixture_policy_sha256':d.get('fixturePolicySHA256'),'fixture_policy_hash_matches':not d.get('fixturePolicy') or hashlib.sha256(json.dumps(d['fixturePolicy'],sort_keys=True,separators=(',',':')).encode()).hexdigest()==d.get('fixturePolicySHA256'),
       'contract_verified':d.get('contractVerified',False),'cleanup':d.get('cleanup'),'operations':[
          {'command':o.get('command'),'input':o.get('input'),'metadata':o.get('metadata'),'error':o.get('error'),'facts':o.get('facts')} for o in ops],
       'all_requests_exact_bucket':all(o.get('input',{}).get('Bucket',d.get('bucket'))==d.get('bucket') for o in ops),
       'request_ids_complete':all(o.get('metadata',{}).get('requestId') for o in ops)})
result['disposable_receipts']=fixtures
result['source_zero_writes_owner_evidence']=index['authorization']
(HERE/'evidence-validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k: v for k,v in result.items() if k not in ['disposable_receipts','commits']},indent=2))
print(json.dumps({'commit_summary':{k:{'head':v['head'],'commits':v['commits'],'files':len(v['files']),'all_match':v['all_match']} for k,v in result['commits'].items()},'disposable_summary':[{k:v for k,v in x.items() if k!='operations'} for x in fixtures]},indent=2))
