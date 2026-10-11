"""Read-only plan for extracted duplicate archives; no deletion or cloud action."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
BASE = Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def checked(path):
    resolved = path.resolve(strict=True)
    assert resolved == path.absolute() and resolved.is_relative_to(BASE)
    assert path.is_file() and not path.is_symlink()
    for parent in [path, *path.parents]:
        if parent.is_relative_to(BASE):
            assert not parent.is_symlink() and not parent.is_junction()
    return resolved


def main():
    candidates = []
    for path in BASE.glob('full*/checks/*/qualified-native/*/remote-evidence/package-sources.tar.gz'):
        number = int(re.match(r'full(\d+)', path.relative_to(BASE).parts[0]).group(1))
        if not 83 <= number <= 114:
            continue
        check = BASE.joinpath(*path.relative_to(BASE).parts[:3])
        terminal_path, stop_path = check / 'terminal-custody.json', check / 'vm-termination.json'
        if not terminal_path.is_file() or not stop_path.is_file():
            continue
        candidates.append((number, path, check, terminal_path, stop_path))
    candidates.sort(key=lambda row: (row[0], str(row[1])))
    assert len(candidates) >= 20
    selected = candidates[:20]
    rows = []; runs = set()
    for number, original, check, terminal_path, stop_path in selected:
        original = checked(original)
        terminal = json.loads(terminal_path.read_bytes()); stopped = json.loads(stop_path.read_bytes())
        assert terminal['run'] == stopped['run'] and terminal['run'] not in runs
        assert terminal['terminal']['native_terminal'] and stopped['custody_verified_before_stop']
        assert stopped['independent']['status'] == 'TERMINATED'
        assert str(stopped['independent']['id']) == '7237681467779354904'
        assert original.parent.parent.name == terminal['run']
        retained = checked(Path(terminal['custody']['repository_path']))
        assert retained.is_relative_to(check) and retained != original
        assert retained.stat().st_size == terminal['custody']['bytes']
        assert digest(retained) == terminal['custody']['remote_sha256']
        raw = original.read_bytes(); original_pin = hashlib.sha256(raw).hexdigest().upper()
        with tarfile.open(retained, 'r:gz') as archive:
            members = archive.getmembers()
            assert members and all(m.isfile() for m in members)
            assert len(members) == len({m.name for m in members})
            package, = [m for m in members if m.name == 'package-sources.tar.gz']
            assert archive.extractfile(package).read() == raw
            native_terminal, = [m for m in members if m.name == 'dedicated-worker-terminal.json']
            owner = json.loads(archive.extractfile(native_terminal).read())
            assert owner['run'] == terminal['run'] and str(owner['host']['id']) == '7237681467779354904'
        with tarfile.open(original, 'r:gz') as package:
            member_count = len(package.getmembers())
            assert member_count > 0
        assert digest(original) == original_pin and digest(retained) == terminal['custody']['remote_sha256']
        rows.append(dict(number=number, run=terminal['run'], remove=str(original), bytes=len(raw), sha256=original_pin,
                         retain_complete_native_archive=str(retained), retained_archive_bytes=retained.stat().st_size,
                         retained_archive_sha256=terminal['custody']['remote_sha256'], retained_member='package-sources.tar.gz',
                         retained_member_bytes=len(raw), retained_member_sha256=original_pin,
                         native_archive_members=len(members), package_source_members=member_count,
                         terminal_receipt=str(terminal_path), terminal_receipt_sha256=digest(terminal_path),
                         independent_stop=str(stop_path), independent_stop_sha256=digest(stop_path),
                         entire_original_member_byte_identity_verified=True,
                         native_archive_custody_unchanged=True))
        runs.add(terminal['run'])
    total = sum(row['bytes'] for row in rows)
    assert total >= 500 * 1024**2 and len({row['remove'] for row in rows}) == 20
    folder = HERE / 'full117-settled-extracted-package-archive-cleanup-plan-v1'
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_bytes(b'* -text\n')
    (folder / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    value = dict(files=rows, count=20, total_bytes=total, free_bytes=shutil.disk_usage(BASE).free,
                 explicit_authorization_required=True, authorization_received=False, files_deleted=False,
                 scope='Only settled extracted package-sources.tar.gz duplicates in the listed qualified-native evidence directories',
                 retention='Every complete retained native archive stays unchanged and contains the exact original package archive bytes; native raw archive custody and all previous one-copy reconciliations are unchanged',
                 latest_full115_full116_archives_and_evidence_excluded=True,
                 unique_source_data_deleted=False, compiler_invoked=False, cloud_operation=False,
                 new_resources=False, admission_guards_unchanged=True,
                 execution_requires_fresh_paths_hashes_and_exact_approval_receipt=True)
    (folder / 'plan.json').write_bytes((json.dumps(value, indent=2) + '\n').encode())
    print(json.dumps(dict(folder=str(folder), count=20, total_bytes=total, plan_sha256=digest(folder / 'plan.json'))), flush=True)


if __name__ == '__main__':
    main()
