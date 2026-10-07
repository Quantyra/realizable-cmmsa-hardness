"""Serialized scoped Git writer. Run only after all local verification succeeds."""
import hashlib,json,os,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'.git').is_dir())
SCOPE='scripts/aws-archive-migration/source-retirement/'
verification=json.loads((HERE/'final4-verification.json').read_text())
assert all(r['exit_code']==0 for r in verification['results'])
lock=REPO/'.git/quantyra-aws-migration-git-writer.lock'
body=json.dumps({'role':'archive-source-production-repair-owner','pid':os.getpid(),'scope':SCOPE}).encode()
deadline=time.monotonic()+120
while True:
    try:fd=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600);break
    except FileExistsError:
        if time.monotonic()>=deadline:raise RuntimeError('GIT_WRITER_LOCK_TIMEOUT; existing lock preserved')
        time.sleep(2)
os.write(fd,body);os.fsync(fd)
def git(*args):
    r=subprocess.run(['git','-c','core.longpaths=true',*args],cwd=REPO,capture_output=True)
    if r.returncode:raise RuntimeError(r.stderr.decode(errors='replace'))
    return r.stdout
try:
    assert not git('diff','--cached','--name-only','-z'),'INDEX_ALREADY_STAGED; refusing to commit others index entries'
    before=git('rev-parse','HEAD').decode().strip()
    git('add','--',SCOPE)
    paths=[x.decode() for x in git('diff','--cached','--name-only','-z').split(b'\0') if x]
    assert paths and all(x.startswith(SCOPE) for x in paths),'OUTSIDE_SCOPE_INDEX'
    # Verify every staged byte against the tested runtime and original evidence bytes.
    for path in paths:
        assert git('show',':'+path)==(REPO/path).read_bytes(),'STAGED_BYTE_DRIFT:'+path
    git('diff','--cached','--check')
    assert paths==[x.decode() for x in git('diff','--cached','--name-only','-z').split(b'\0') if x]
    assert all(x.startswith(SCOPE) for x in paths),'OUTSIDE_SCOPE_INDEX_IMMEDIATELY_BEFORE_COMMIT'
    git('commit','-m','Repair archive production endpoint provenance and bucket continuity')
    commit=git('rev-parse','HEAD').decode().strip()
    assert set(git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines())==set(paths)
    for path in paths:assert git('show',commit+':'+path)==(REPO/path).read_bytes()
    result={'commit':commit,'before_head':before,'lock':str(lock),'acquisition':'CreateNew / O_EXCL bounded 120 seconds','staged_paths':paths,'only_owned_scope':True,'index_initially_empty':True,'staged_and_commit_bytes_equal_runtime':True,'parent_commit':False,'push':False}
    print(json.dumps(result))
finally:
    os.close(fd)
    if lock.read_bytes()==body:lock.unlink()
