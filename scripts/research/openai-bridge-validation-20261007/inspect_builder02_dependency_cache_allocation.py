"""Read-only allocation inventory; does not assert byte equality or recovery clearance."""
import json
import re
import sys
import urllib.request
from collections import defaultdict
from pathlib import Path

HOME = Path('/home/dfredriksen_quantyra_org')


def main():
    assert sys.platform == 'linux' and Path.home().resolve() == HOME
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    def metadata(key):
        request = urllib.request.Request('http://metadata.google.internal/computeMetadata/v1/instance/'+key,
                                         headers={'Metadata-Flavor': 'Google'})
        with opener.open(request, timeout=10) as response:
            assert response.headers.get('Metadata-Flavor') == 'Google'
            return response.read().decode()
    assert metadata('id') == '7237681467779354904'
    assert metadata('name') == 'quantyra-lean-builder-02'
    runs = []
    for run in sorted(HOME.glob('cmmsa_a8_output_*')):
        if not re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}', run.name) or run.is_symlink():
            continue
        packages = run/'.lake/packages'
        if not packages.is_dir() or packages.is_symlink():
            continue
        groups = defaultdict(lambda: dict(files=0, allocated_bytes=0, logical_bytes=0))
        for path in packages.rglob('*'):
            try:
                if path.is_symlink() or not path.is_file():
                    continue
                info = path.stat()
            except FileNotFoundError:
                continue  # A concurrently running, separately guarded recovery may rename a duplicate.
            rel = path.relative_to(packages)
            category = 'build' if {'.lake', 'build'} <= set(rel.parts) else 'other'
            key = category+':'+path.suffix
            row = groups[key]
            row['files'] += 1
            row['allocated_bytes'] += info.st_blocks*512
            row['logical_bytes'] += info.st_size
        runs.append(dict(run=run.name, groups=dict(groups)))
    print(json.dumps(dict(vm='quantyra-lean-builder-02', id='7237681467779354904', runs=runs,
                          read_only=True, concurrent_snapshot=True, byte_equality_verified=False,
                          recovery_clearance=False, compiler_invoked=False)))


if __name__ == '__main__':
    main()
