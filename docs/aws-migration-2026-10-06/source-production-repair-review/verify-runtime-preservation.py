import hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
OWN=REPO/'scripts/aws-archive-migration/source-retirement/evidence/production-repair'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
runtime=read(OWN/'runtime-file-hashes-final.json');witness=read(OWN/'runtime-final4.json');result={}
assert sha(OWN/'runtime-file-hashes-final.json')==witness['runtime_inventory_sha256']
failed=[]
for x in runtime['runtime_files']:
    p=Path(x['path'])
    if sha(p)!=x['sha256'] or p.stat().st_size!=x['bytes']:failed.append(str(p))
result['runtime']={'files':len(runtime['runtime_files']),'all_match':not failed,'failures':failed,'inventory_sha256':sha(OWN/'runtime-file-hashes-final.json')}
prior=read(OWN/'preservation-check.json')['old_own_evidence_and_review_files'];failed=[]
for x in prior:
    p=Path(x['file']);p=p if p.is_absolute() else REPO/p
    if sha(p)!=x['sha256']:failed.append(str(p))
result['prior_own_and_review_evidence']={'files':len(prior),'all_match':not failed,'failures':failed}
original=read(REPO/'docs/aws-migration-2026-10-06/source-lifecycle-review/evidence-index.json')
failed=[]
for x in original['audit_files']:
    p=Path(x['path'])
    if sha(p)!=x['sha256'] or p.stat().st_size!=x['bytes']:failed.append(str(p))
result['original_review_artifacts']={'files':len(original['audit_files']),'all_match':not failed,'failures':failed}
(HERE/'runtime-preservation-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
