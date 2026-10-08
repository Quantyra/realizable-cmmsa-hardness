"""Inspect exact upstream build pins against Full89; never execute Lake/Lean."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import tarfile
from urllib.request import urlopen

PIN = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
ROOT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02')

def sha(data):
    return hashlib.sha256(data).hexdigest().upper()

def main():
    sources = {}
    records = []
    for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json'):
        url = 'https://raw.githubusercontent.com/openai/math/' + PIN + '/lean/' + name
        with urlopen(url, timeout=30) as response:
            data = response.read()
        sources[name] = data
        records.append(dict(path='lean/'+name, url=url, sha256=sha(data), bytes=len(data)))
    upstream = json.loads(sources['lake-manifest.json'])
    with tarfile.open(ROOT/'input-archive.tar.gz') as archive:
        local_toolchain = archive.extractfile('lean-toolchain').read()
        local_manifest_bytes = archive.extractfile('lake-manifest.json').read()
    local = json.loads(local_manifest_bytes)
    upstream_packages = {row['name']: row for row in upstream['packages']}
    local_packages = {row['name']: row for row in local['packages']}
    comparison = {name: dict(upstream_revision=row.get('rev'), local_revision=local_packages.get(name, {}).get('rev'),
        revision_equal=row.get('rev') == local_packages.get(name, {}).get('rev'))
        for name, row in upstream_packages.items() if name in local_packages}
    report = dict(observed_utc=datetime.now(timezone.utc).isoformat(), upstream_commit=PIN, files=records,
        upstream_toolchain=sources['lean-toolchain'].decode().strip(),
        local_resource=ROOT.name, local_toolchain=local_toolchain.decode().strip(),
        toolchain_equal=sources['lean-toolchain'].decode().strip() == local_toolchain.decode().strip(),
        local_lake_manifest_sha256=sha(local_manifest_bytes), upstream_dependency_count=len(upstream_packages),
        local_dependency_count=len(local_packages), shared_dependency_comparison=comparison,
        upstream_requires_compatibility_patch_handling='preResolutionPatchNames' in sources['lakefile.lean'].decode(),
        compiler_executed=False, upstream_closure_verified=False, local_capsule_modified=False,
        scope='Build-configuration inspection only. Use exact upstream compiler/configuration/dependencies and patch identities in a separate GCP context; do not substitute CMMSA cached objects.')
    destination = Path(__file__).with_name('upstream-build-pin-inspection.json')
    with destination.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
