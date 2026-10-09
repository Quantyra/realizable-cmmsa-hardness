"""Read-only, exact-VM observation; never starts or repeats compilation."""
import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
from finalize_builder02_bootstrap import SDK, FLAGS

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full97-spectral-bridge-utf8-section-repair-resource02')
VM = 'quantyra-lean-builder-02'
RUN = 'cmmsa_a8_output_20261009T050952Z_3a6b1f17'
REMOTE = '''import json,pathlib,subprocess,shutil,urllib.request,re
home=pathlib.Path('/home/dfredriksen_quantyra_org')
run=RUN_VALUE
opener=urllib.request.build_opener(urllib.request.ProxyHandler({}))
request=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
with opener.open(request,timeout=10) as response:
    assert response.headers.get('Metadata-Flavor')=='Google'
    identity=response.read().decode()
assert identity=='7237681467779354904'
base=home/(run+'_evidence')
marker=home/'full97-spectral-bridge-utf8-section-repair-resource02-launch-once.json'
rows={p.name:p.read_text().strip() for p in base.glob('stage-*.native-exit')}
procs=subprocess.run(['ps','-eo','pid=,comm=,etime=,rss=,args='],capture_output=True,text=True,check=True).stdout
active=[r for r in procs.splitlines() if len(r.split())>=2 and (r.split()[1] in ('lean','lake','cp') or ('full97_worker.py' in r or 'cloud_capture.py' in r) and r.split()[1]=='python3')]
errors={}
for p in sorted(base.glob('stage-*.std*')):
    text=p.read_text(errors='replace')
    headers=[line for line in text.splitlines() if re.match(r'^.*(?:\\.lean:[0-9]+:[0-9]+: error:|^error:)',line)]
    if headers:errors[p.name]={'count':len(headers),'last_headers':headers[-8:]}
print(json.dumps(dict(run=run,verified_VM_id=identity,remote_launch_marker_exists=marker.exists(),evidence_directory=str(base),stage_exits=rows,terminal_exists=(base/'dedicated-worker-terminal.json').exists(),active_processes=active,diagnostic_headers=errors,free_bytes=shutil.disk_usage(home).free,qualification=False)))
'''


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    if marker['run'] != RUN:
        raise RuntimeError('Observer is bound to a different immutable attempt')
    folder = ROOT / 'observations' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True)
    code = REMOTE.replace('RUN_VALUE', repr(RUN))
    command = 'python3 -B -c ' + shlex.quote(
        "import base64;exec(base64.b64decode('" + base64.b64encode(code.encode()).decode() + "'))")
    argv = [SDK, 'compute', 'ssh', VM, '--tunnel-through-iap', '--command=' + command, *FLAGS]
    child = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             creationflags=subprocess.CREATE_NO_WINDOW)
    while True:
        try:
            out, err = child.communicate(timeout=30)
            break
        except subprocess.TimeoutExpired:
            print('Following same read-only observer', child.pid, flush=True)
    (folder / 'stdout.json').write_bytes(out)
    (folder / 'stderr.txt').write_bytes(err)
    value = dict(argv=argv, native_exit=child.returncode,
        observer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest().upper(),
        stdout_sha256=hashlib.sha256(out).hexdigest().upper(),
        other_VM_modified=False, compiler_launched=False, qualification=False)
    (folder / 'receipt.json').write_bytes((json.dumps(value, indent=2) + '\n').encode())
    print('Observation:', folder, 'native:', child.returncode, flush=True)
    print(out.decode(errors='replace'), flush=True)
    print(err.decode(errors='replace'), flush=True)
    if child.returncode:
        raise SystemExit(child.returncode)


if __name__ == '__main__':
    main()
