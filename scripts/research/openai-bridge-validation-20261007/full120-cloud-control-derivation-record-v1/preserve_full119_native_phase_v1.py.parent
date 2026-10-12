"""Preserve exact terminal or final custody without launching any cloud action."""
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tarfile
from custody_checks import digest, verify_local_custody
from full119_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent
RUN = None


def main(phase):
    global RUN
    assert phase in ('terminal', 'final')
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    RUN = marker['run']
    import re
    assert re.fullmatch(r'cmmsa_a8_output_\d{8}T\d{6}Z_[a-f0-9]{8}', RUN)
    check = Path(marker['preflight']).resolve(strict=True)
    assert check.is_relative_to((ROOT / 'checks').resolve())
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    assert receipt['run'] == RUN and receipt['terminal']['native_terminal']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'],
                         custody['remote_sha256'], custody['bytes'])
    paths = {ROOT / 'launch-once.json', ROOT / 'start-once.json', Path(__file__).resolve()}
    paths.update(p for p in (ROOT/'staging-controls').rglob('*') if p.is_file())
    paths.update(p for p in check.rglob('*') if p.is_file() and 'remote-evidence' not in p.parts)
    wrappers = []
    native_wrappers = []
    stop_wrappers = []
    audit_wrappers = []
    for folder in sorted((ROOT / 'research-resume-20261011').iterdir()):
        command_path = folder / 'command.json'
        if not command_path.is_file():
            continue
        record = json.loads(command_path.read_bytes())
        action = record['argv'][7:]
        name = Path(action[0]).name
        selected = name in ('run_full119_native_openssh_v1.py', 'inspect_full119_native_progress_v1.py')
        selected |= phase == 'final' and (name == 'terminate_full119_after_custody_openssh_v1.py' or
                                         name == 'full119_postprocess.py' and action[1:] == ['audit'])
        if not selected:
            continue
        assert 'native_exit' in record, ('Original handle still live', folder)
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == record[stream + '_sha256']
        row = dict(folder=str(folder), action=action, native_exit=record['native_exit'], child_pid=record['pid'])
        wrappers.append(row)
        if name == 'run_full119_native_openssh_v1.py':
            assert record['native_exit'] == (0 if receipt['terminal']['compile_green'] else 1)
            native_wrappers.append(row)
        elif name == 'terminate_full119_after_custody_openssh_v1.py':
            assert record['native_exit'] == 0
            stop_wrappers.append(row)
        elif name == 'full119_postprocess.py':
            assert record['native_exit'] in (0, 1)
            audit_wrappers.append(row)
        else:
            assert record['native_exit'] == 0
        paths.update(p for p in folder.rglob('*') if p.is_file())
    assert len(native_wrappers) == 1
    stop = None
    if phase == 'final':
        assert len(stop_wrappers) == len(audit_wrappers) == 1
        stop = json.loads((check / 'vm-termination.json').read_bytes())
        assert stop['run'] == RUN and stop['custody_verified_before_stop']
        assert stop['independent']['status'] == 'TERMINATED'
        assert str(stop['independent']['id']) == VM_ID and not stop['other_vm_modified']
    for folder in ((ROOT / 'live-native-inspections-v1').iterdir() if (ROOT / 'live-native-inspections-v1').exists() else []):
        assert (folder / 'inspection.json').is_file()
        for record in json.loads((folder / 'transport/commands.json').read_bytes()):
            assert record['native_exit'] == 0
            for stream in ('stdout', 'stderr'):
                assert digest(Path(record[stream + '_path'])) == record[stream + '_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
    with tarfile.open(custody['repository_path'], 'r:gz') as archive:
        members = archive.getmembers()
        assert members and all(m.isfile() for m in members)
        assert len(members) == len({m.name for m in members})
        for extracted in check.glob('qualified-native/*/remote-evidence'):
            assert {p.relative_to(extracted).as_posix() for p in extracted.rglob('*') if p.is_file()} == {m.name for m in members}
            for member in members:
                assert (extracted / member.name).read_bytes() == archive.extractfile(member).read()
    total = sum(p.stat().st_size for p in paths)
    assert shutil.disk_usage(HERE).free - total >= 1536 * 1024**2 + 64 * 1024**2
    target = HERE / ('full119-native-' + phase + '-custody-v1')
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    payload = target / 'complete-originals.tar.gz'
    rows = []
    with tarfile.open(payload, 'x:gz') as archive:
        for i, path in enumerate(sorted(paths)):
            pin = digest(path)
            member = f'{i:03d}-' + path.name
            archive.add(path, arcname=member, recursive=False)
            assert digest(path) == pin
            rows.append(dict(original=str(path), member=member, bytes=path.stat().st_size, sha256=pin))
    with tarfile.open(payload, 'r:gz') as archive:
        assert len(archive.getmembers()) == len(rows)
        for row in rows:
            data = archive.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
            assert digest(Path(row['original'])) == row['sha256']
    value = dict(schema='full119-native-phase-complete-custody-v1', phase=phase, run=RUN,
                 files=rows, payload=dict(file=payload.name, bytes=payload.stat().st_size, sha256=digest(payload)),
                 wrappers=wrappers, original_native_child_pid=native_wrappers[0]["child_pid"], terminal_receipt=receipt,
                 independent_stop=stop, every_original_member_roundtrip_verified=True,
                 native_archive_members=len(members), native_archive_sha256=custody['remote_sha256'],
                 fresh_original_two_copy_custody_verified=True, compiler_replayed=False,
                 cloud_action_performed=False, mathematical_acceptance=False, full_goal_complete=False)
    value['prior_complete_custody'] = {
        name: digest(HERE / name / 'index.json') for name in
        ('full119-preparation-offline-record-v1', 'full118-recovery-complete-record-v5')}
    (target / 'index.json').open('x').write(json.dumps(value, indent=2) + '\n')
    print(json.dumps(dict(folder=str(target), originals=len(rows), payload_bytes=payload.stat().st_size,
                         payload_sha256=digest(payload))), flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
