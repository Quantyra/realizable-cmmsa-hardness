"""Read-only duplicate cleanup plan with retained raw archives and exact Git members."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BUILDERS = Path('C:/Users/dfred/.quantyra/builder02')


def main():
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=REPO)
    head = git('rev-parse', 'HEAD').decode().strip()
    assert head == git('rev-parse', 'origin/research/openai-bridge-validation-20261007').decode().strip()
    tree = {}
    for entry in git('ls-tree', '-rz', head).split(b'\0'):
        if not entry:
            continue
        meta, path = entry.split(b'\t', 1)
        mode, kind, oid = meta.split()
        if kind == b'blob':
            tree[path.decode()] = oid.decode()
    verified = {}

    def committed(path, pin=None):
        path = path.resolve(strict=True)
        assert path.is_relative_to(REPO.resolve())
        rel = path.relative_to(REPO).as_posix()
        if rel not in verified:
            raw = path.read_bytes()
            oid = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            assert tree[rel] == oid, 'Worktree bytes differ from committed Git blob'
            verified[rel] = dict(path=str(path), relative=rel, bytes=len(raw),
                                 sha256=hashlib.sha256(raw).hexdigest().upper(), git_blob=oid)
        row = verified[rel]
        assert pin is None or row['sha256'] == pin
        return row

    by_pin = {}
    for pattern in ('*/preservation.json', '*/index.json'):
        for index in HERE.glob(pattern):
            match = re.match(r'full(\d+)', index.parent.name)
            if not match or not 100 <= int(match[1]) <= 113:
                continue
            if index.relative_to(REPO).as_posix() not in tree:
                continue
            committed(index)
            value = json.loads(index.read_bytes())
            for row in value.get('records', value.get('files', [])):
                if not isinstance(row, dict) or not row.get('sha256'):
                    continue
                rel = row.get('copy', row.get('target', row.get('path')))
                if not isinstance(rel, str):
                    continue
                path = index.parent / rel
                if path.is_file() and path.relative_to(REPO).as_posix() in tree:
                    by_pin.setdefault(row['sha256'], []).append((path, index))
    base = Path('C:/a8gcp').resolve(strict=True)
    rows = []
    excluded = []
    for root in sorted(BUILDERS.iterdir()):
        match = re.match(r'full(\d+)-', root.name)
        if not match or not 100 <= int(match[1]) <= 113:
            continue
        try:
            marker = json.loads((root / 'launch-once.json').read_bytes())
            check = Path(marker['preflight']).resolve(strict=True)
            receipt_path = check / 'terminal-custody.json'
            stop_path = check / 'vm-termination.json'
            receipt = json.loads(receipt_path.read_bytes())
            stop = json.loads(stop_path.read_bytes())
            assert marker['run'] == receipt['run'] == stop['run']
            assert receipt['terminal']['native_terminal']
            assert stop['independent']['status'] == 'TERMINATED'
            assert str(stop['independent']['id']) == '7237681467779354904'
            custody = receipt['custody']
            short = Path(custody['short_path']).resolve(strict=True)
            original = Path(custody['repository_path']).resolve(strict=True)
            assert short.parent == base and original.is_relative_to(check) and short != original
            pin = custody['remote_sha256']
            assert short.stat().st_size == original.stat().st_size == custody['bytes']
            assert digest(short) == digest(original) == pin
            members = []
            with tarfile.open(original, 'r:gz') as archive:
                entries = archive.getmembers()
                assert len({m.name for m in entries}) == len(entries)
                for member in entries:
                    assert member.isfile()
                    raw = archive.extractfile(member).read()
                    member_pin = hashlib.sha256(raw).hexdigest().upper()
                    candidates = by_pin.get(member_pin, [])
                    assert candidates, 'No committed extracted member for ' + member.name
                    path, index = candidates[0]
                    retained = committed(path, member_pin)
                    assert retained['bytes'] == member.size
                    members.append(dict(member=member.name, **retained, custody_index=str(index),
                                        custody_index_sha256=digest(index)))
            rows.append(dict(remove=str(short), bytes=custody['bytes'], sha256=pin,
                             retain_original=str(original), run=marker['run'],
                             terminal_receipt=str(receipt_path), terminal_receipt_sha256=digest(receipt_path),
                             independent_stop=str(stop_path), independent_stop_sha256=digest(stop_path),
                             retained_committed_members=members, all_native_members_exact=True))
        except (AssertionError, KeyError, OSError, ValueError, tarfile.TarError) as error:
            excluded.append(dict(root=str(root), reason=type(error).__name__ + ': ' + str(error)))
    assert rows and len({r['remove'] for r in rows}) == len(rows)
    assert git('rev-parse', 'HEAD').decode().strip() == head
    out = HERE / 'full115-redundant-native-copy-cleanup-plan-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (out / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    plan = dict(head=head, files=rows, excluded=excluded, total_bytes=sum(r['bytes'] for r in rows),
                free_bytes=shutil.disk_usage(HERE).free,
                action='Remove only the listed redundant C:/a8gcp copies after explicit user authorization',
                each_raw_original_archive_retained=True, every_native_member_retained_in_exact_committed_file=True,
                committed_and_pushed_custody_verified=True, no_claim_of_second_identical_compressed_archive=True,
                current_Full114_excluded=True, files_deleted=False, authorization_received=False)
    (out / 'plan.json').open('x').write(json.dumps(plan, indent=2) + '\n')
    print(json.dumps(dict(folder=out.name, candidates=len(rows), total_bytes=plan['total_bytes'],
                         exclusions=excluded, files_deleted=False)), flush=True)


if __name__ == '__main__':
    main()
