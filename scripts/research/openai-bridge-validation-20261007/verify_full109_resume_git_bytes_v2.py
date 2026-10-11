"""Verify every preserved original against actual staged or committed Git bytes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
name, revision = sys.argv[1:]
assert Path(name).name == name and name.startswith('full109-resume-')
assert revision in ('HEAD', 'INDEX')
folder = here/name
repo = here.parents[2]
rows = json.loads((folder/'index.json').read_bytes())['files']
prefix = '' if revision == 'INDEX' else 'HEAD'
queries = ''.join(prefix+':'+(folder/row['copy']).relative_to(repo).as_posix()+'\n' for row in rows).encode()
result = subprocess.run(['git', 'cat-file', '--batch'], cwd=repo, input=queries, capture_output=True, check=True)
data = result.stdout
offset = 0
for row in rows:
    end = data.index(b'\n', offset)
    header = data[offset:end].split()
    assert header[1] == b'blob'
    size = int(header[2])
    blob = data[end+1:end+1+size]
    assert data[end+1+size:end+2+size] == b'\n'
    offset = end+2+size
    assert len(blob) == row['bytes'] and hashlib.sha256(blob).hexdigest().upper() == row['sha256']
assert offset == len(data)
print(json.dumps(dict(record=name, revision=revision, original_byte_identities_verified=len(rows))))
