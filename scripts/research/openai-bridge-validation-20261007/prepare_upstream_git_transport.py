"""Freeze all original dependency Git stores for isolated Linux checkout, no Lean."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

BASE = Path('C:/Users/dfred/.quantyra/upstream')
DEST = BASE/'original42-git-transport-v1'


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest().upper()


def main():
    audit = json.loads((BASE/'original-dependencies-recovery-v1/all42-source-custody-audit.json').read_bytes())
    assert audit['packages_verified'] == 42 and audit['all42_dependency_sources_recovered']
    stores = []
    for row in audit['packages']:
        receipt = Path(row['receipt_path'])
        assert digest(receipt) == row['receipt_sha256']
        assert digest(Path(row['archive_path'])) == row['archive_sha256']
        repo = receipt.parent/'repository.git'
        pin = row['package']['rev']
        head = subprocess.check_output(['git', '--git-dir='+str(repo), 'rev-parse', 'HEAD']).decode().strip()
        assert head == pin
        name = row['package']['name'].strip('«»')
        assert '/' not in name and '\\' not in name and name not in ('.', '..')
        stores.append((name, repo, row['package']))
    assert len({s[0] for s in stores}) == 42
    size = sum(p.stat().st_size for _, r, _ in stores for p in r.rglob('*') if p.is_file())
    assert shutil.disk_usage(BASE).free > 1536*1024**2 + size
    DEST.mkdir()
    archive = DEST/'original42-git-stores.tar.gz'
    with tarfile.open(archive, 'x:gz') as t:
        for name, repo, _ in stores:
            t.add(repo, arcname='git-stores/'+name+'.git')
    receipt = dict(schema='original42-git-transport-v1', packages=[p for _, _, p in stores],
                   archive_path=str(archive), archive_bytes=archive.stat().st_size,
                   archive_sha256=digest(archive), all42_heads_verified=True,
                   linux_checkout_verified=False, patches_applied=False, compiled=False, accepted=False)
    (DEST/'manifest.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'packages'}), flush=True)


if __name__ == '__main__':
    main()
