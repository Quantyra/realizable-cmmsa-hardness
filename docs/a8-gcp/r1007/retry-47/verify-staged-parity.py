"""Read-only parity of every staged blob against exact current bytes."""
import subprocess, hashlib, json
from pathlib import Path
repo=Path(__file__).resolve().parents[4]
staged=subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=repo).decode().strip('\0').split('\0')
index={r.split('\t',1)[1]:r.split()[1] for r in subprocess.check_output(['git','ls-files','--stage'],cwd=repo).decode().splitlines()}
for n in staged:
    data=(repo/n).read_bytes()
    assert index[n]==hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),n
print(json.dumps({'staged_files':len(staged),'exact_byte_parity':True}))
