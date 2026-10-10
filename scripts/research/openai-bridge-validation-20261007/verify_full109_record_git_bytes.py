"""Batch verify preserved record blobs against their original byte indexes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
here=Path(__file__).parent
name=sys.argv[1]
assert Path(name).name==name and name.startswith('full109-')
folder=here/name;repo=here.parents[2]
rows=json.loads((folder/'index.json').read_bytes())['records']
queries=''.join('HEAD:'+(folder/row['target']).relative_to(repo).as_posix()+'\n' for row in rows).encode()
process=subprocess.run(['git','cat-file','--batch'],cwd=repo,input=queries,capture_output=True,check=True)
data=process.stdout;offset=0
for row in rows:
    end=data.index(b'\n',offset);header=data[offset:end].split()
    assert header[1]==b'blob'
    size=int(header[2]);blob=data[end+1:end+1+size]
    assert data[end+1+size:end+2+size]==b'\n'
    offset=end+2+size
    assert len(blob)==row['bytes'] and hashlib.sha256(blob).hexdigest().upper()==row['sha256']
assert offset==len(data)
print(json.dumps(dict(record=name,committed_original_byte_identities_verified=len(rows))))
