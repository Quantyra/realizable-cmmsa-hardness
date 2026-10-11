"""Archive complete new recovery custody after its independent all-seven audit."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest
from full110_builder02_controller import ROOT
from audit_full110_settled_cache_recovery_v2 import AUDIT, RECOVERY, validate_local_audit

HERE = Path(__file__).resolve().parent
NEXT = ROOT.parent / 'full111-exact-real-complex-operators-repair-resource02'
WRAPPERS = [
    ('20261011T032805725979Z-0ef6eb4331d3', 11904),
    ('20261011T033708144193Z-53c06f68e63c', 20450),
    ('20261011T033945565433Z-9b91740922d4', 91730),
    ('20261011T034026430747Z-85bea84f468b', 58088)]


def main():
    audit = validate_local_audit()
    assert not (NEXT / 'launch-once.json').exists()
    paths = {Path(__file__).resolve()}
    handles = []
    wrappers = [(ROOT / 'research-resume-20261011' / name, handle) for name, handle in WRAPPERS]
    audit_wrappers = []
    for path in (NEXT / 'research-resume-20261011').glob('*/command.json'):
        row = json.loads(path.read_bytes())
        if row['argv'][-1].endswith('audit_full110_settled_cache_recovery_v2.py'):
            audit_wrappers.append(path.parent)
    assert len(audit_wrappers) == 1
    wrappers.append((audit_wrappers[0], 'original audit wrapper; tool handle recorded in planning'))
    for folder, handle in wrappers:
        command = json.loads((folder / 'command.json').read_bytes())
        assert command['native_exit'] == 0
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == command[stream + '_sha256']
        paths.update(path for path in folder.iterdir() if path.is_file())
        handles.append(dict(handle=handle, wrapper=str(folder), native_exit=0))
    folders = [RECOVERY / '20261011T033825083308Z', AUDIT]
    for operation in RECOVERY.glob('*/operation-91.json'):
        if json.loads(operation.read_bytes())['action'] == 'execute':
            folders.append(operation.parent)
    assert len(folders) == 3
    for idle in (RECOVERY / 'idle-refresh-controls').glob('*/idle-refreshed.json'):
        if idle.parent.name != '20261011T031803853320Z':
            folders.append(idle.parent)
    assert len(folders) == 5
    for folder in folders:
        for row in json.loads((folder / 'commands.json').read_bytes()):
            assert row['native_exit'] == 0 and not row['timed_out']
            for stream in ('stdout', 'stderr'):
                assert digest(folder / row[stream + '_path']) == row[stream + '_sha256']
        paths.update(path for path in folder.rglob('*') if path.is_file())
    previous = []
    for name, commit in [('full110-recovery-lifecycle-start-v1', '54d4c152'),
                         ('full110-recovery-plans-record-v1', 'ce6c45be'),
                         ('full110-recovery-execution-interruption-v1', 'f20588a3')]:
        index = HERE / name / 'index.json'
        for row in json.loads(index.read_bytes())['files']:
            assert digest(index.parent / row['copy']) == row['sha256']
        previous.append(dict(folder=name, preserved_commit=commit, index_sha256=digest(index)))
    assert shutil.disk_usage(HERE).free - sum(path.stat().st_size for path in paths) >= 1536 * 1024**2
    destination = HERE / 'full110-complete-recovery-record-v2'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').open('x', encoding='utf-8').write('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    archive_path = destination / 'complete-originals.tar.gz'
    rows = []
    with tarfile.open(archive_path, 'x:gz', format=tarfile.PAX_FORMAT) as archive:
        for number, original in enumerate(sorted(paths)):
            member = f'{number:03d}-' + original.name
            row = dict(original=str(original), member=member, bytes=original.stat().st_size, sha256=digest(original))
            info = tarfile.TarInfo(member)
            info.size, info.mode, info.mtime = row['bytes'], 0o644, 0
            with original.open('rb') as stream:
                archive.addfile(info, stream)
            assert digest(original) == row['sha256']
            rows.append(row)
    with tarfile.open(archive_path, 'r:gz') as archive:
        members = archive.getmembers()
        assert [member.name for member in members] == [row['member'] for row in rows]
        for member, row in zip(members, rows):
            assert member.isfile() and member.size == row['bytes']
            with archive.extractfile(member) as stream:
                assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == row['sha256']
    result = dict(schema='full110-complete-recovery-custody-v2', members=rows, previous_exact_custody=previous,
        wrappers=handles, independent_audit=audit, all_seven_scopes_settled=True,
        original_50622_failure_preserved_as_exit_1=True, scope90_collected_without_replay=True,
        archive=dict(file=archive_path.name, bytes=archive_path.stat().st_size, sha256=digest(archive_path)),
        all_archive_members_verified=True, unique_originals_deleted=False,
        compiler_invoked=False, mathematical_acceptance=False)
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    assert shutil.disk_usage(HERE).free >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(destination), complete_originals=len(rows), archive=result['archive'],
                         remote_disk_available_bytes=audit['disk_available_bytes'])), flush=True)


if __name__ == '__main__':
    main()
