"""Read-only bounded transport of the already-complete cloud archive; never compiles."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import base64, json, shutil, sys
from runner import Control, VM
from common import PACKAGE, write_new, json_bytes, file_sha, utc

run = PACKAGE / 'runs' / sys.argv[1]
folder = run / 'bounded-custody'
folder.mkdir()
remote = '/home/dfredriksen_quantyra_org/cmmsa-evidence/' + run.name + '-evidence.tar.gz'
expected = '697485177C9B02B0DF3F3892B2E0C3C7D02C52F4A699B55802B32B2276CB2F72'
size = 38272740
block = 4 * 1024 * 1024
def fetch(index):
    part = folder / str(index)
    part.mkdir()
    control = Control(part)
    control.authenticated = True
    command = 'dd if=' + remote + ' bs=' + str(block) + ' skip=' + str(index) + ' count=1 status=none | base64 -w0'
    code, output, _ = control.cloud(['compute','ssh',VM,'--tunnel-through-iap','--command='+command],timeout=120)
    data = base64.b64decode(output,validate=True)
    assert len(data) == min(block,size-index*block)
    write_new(part/'archive.part',data)
    print('Verified chunk',index,len(data),flush=True)
    return part/'archive.part'
with ThreadPoolExecutor(max_workers=3) as pool:
    paths = list(pool.map(fetch,range((size+block-1)//block)))
short = Path('C:/a8gcp') / (run.name[-8:] + '-bounded.tar.gz')
with short.open('xb') as stream:
    for path in paths:stream.write(path.read_bytes())
assert short.stat().st_size == size and file_sha(short) == expected
repository = run / (run.name + '-evidence.tar.gz')
shutil.copyfile(short,repository)
assert file_sha(repository) == expected
write_new(run/'bounded-custody.json',json_bytes({'verified_utc':utc(),'before_stop':True,
    'short_path':str(short),'repository_path':str(repository),'short_sha256':file_sha(short),
    'repository_sha256':file_sha(repository),'remote_sha256':expected,'remote_bytes':size,
    'source_receipt':'transfer-observation/commands.json','compiler_restarted':False,
    'reason':'Original SCP stalled with no file growth; retained unchanged. Read-only archive chunks.'}))
print('CUSTODY VERIFIED',expected,flush=True)
