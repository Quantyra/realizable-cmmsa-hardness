"""Verify a completed transfer before extracting selected dependencies on GCP."""
import json
from pathlib import Path
import re
import sys
import tarfile
import urllib.request
from verify_builder02 import digest

def extract(stage, expected_sha, expected_size):
    if sys.platform != 'linux': raise RuntimeError('GCP Linux required')
    request=urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/id',headers={'Metadata-Flavor':'Google'})
    opener=urllib.request.build_opener(urllib.request.ProxyHandler({}))
    with opener.open(request,timeout=10) as response:
        if response.headers.get('Metadata-Flavor') != 'Google' or response.read().decode().strip() != '7237681467779354904':
            raise RuntimeError('Unexpected GCP host')
    if not re.fullmatch('[A-F0-9]{64}',expected_sha): raise ValueError('Invalid digest')
    home=Path.home().resolve()
    if str(home) != '/home/dfredriksen_quantyra_org': raise RuntimeError('Unexpected home')
    stage=Path(stage).resolve(strict=True)
    archive_path=stage/'dependencies.tar.gz'
    if archive_path.stat().st_size != int(expected_size) or digest(archive_path) != expected_sha:
        raise RuntimeError('Transferred archive identity mismatch')
    warm='cmmsa_a8_output_20261007T230522Z_6af6dc24'
    if (home/'.elan').exists() or (home/warm).exists(): raise RuntimeError('Dependency destination already exists; inspect before continuing')
    allowed=('.elan/bin','.elan/settings.toml','.elan/toolchains/leanprover--lean4---v4.34.0-rc2',warm+'/.lake')
    with tarfile.open(archive_path,'r:gz') as archive:
        members=archive.getmembers()
        names=[m.name.rstrip('/') for m in members]
        if len(names) != len(set(names)): raise RuntimeError('Duplicate dependency entries')
        for name in names:
            if not any(name == prefix or name.startswith(prefix+'/') for prefix in allowed):
                raise RuntimeError('Unselected dependency path: '+name)
            if name.startswith('/') or any(part in ('','.','..') for part in name.split('/')):
                raise RuntimeError('Unsafe dependency path')
        archive.extractall(home,members=members,filter='data')
    receipt=dict(archive_sha256=expected_sha,archive_bytes=int(expected_size),members=len(members),compiler_invoked=False)
    (stage/'dependency-extraction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__': extract(*sys.argv[1:])
