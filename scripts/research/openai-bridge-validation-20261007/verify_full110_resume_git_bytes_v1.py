"""Compare an explicitly named current evidence folder with original INDEX or HEAD blobs."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
ALLOWED = {'full110-resume-staging-failure-v1', 'full110-resume-staging-success-v1', 'numeric-no-offer-capture-v1',
           'numeric-no-offer-capture-v2', 'actual-numeric-no-candidate-v1', 'actual-numeric-no-candidate-v2'}


def main():
    name, revision = sys.argv[1:]
    assert name in ALLOWED and revision in ('INDEX', 'HEAD')
    folder = HERE / name
    paths = sorted(p for p in folder.rglob('*') if p.is_file())
    assert paths
    prefix = '' if revision == 'INDEX' else 'HEAD'
    queries = ''.join(prefix+':'+p.relative_to(REPO).as_posix()+'\n' for p in paths).encode()
    result = subprocess.run(['git', 'cat-file', '--batch'], cwd=REPO, input=queries, capture_output=True, check=True)
    offset = 0
    for path in paths:
        end = result.stdout.index(b'\n', offset)
        header = result.stdout[offset:end].split()
        assert header[1] == b'blob'
        size = int(header[2])
        data = result.stdout[end+1:end+1+size]
        assert result.stdout[end+1+size:end+2+size] == b'\n'
        offset = end+2+size
        assert data == path.read_bytes()
    assert offset == len(result.stdout)
    print(json.dumps(dict(folder=name, revision=revision, exact_original_blobs_verified=len(paths))))


if __name__ == '__main__':
    main()
