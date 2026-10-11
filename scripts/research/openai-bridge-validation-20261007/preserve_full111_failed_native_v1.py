"""Preserve complete failed native, guarded stop, and unchanged red audit originals."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest, verify_local_custody
from full111_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent
WRAPPERS = [('20261011T035530486815Z-56b79f751c14', 60064, 1),
            ('20261011T040646428071Z-4b510d9eb357', 28272, 0),
            ('20261011T041028768897Z-7f57c25d74f1', 23769, 1)]


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert marker['run'] == receipt['run'] == stop['run'] == 'cmmsa_a8_output_20261011T035621Z_498f7ba6'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [r['native_exit'] for r in receipt['terminal']['stages']] == [0, 0, 0, 0, 1, 125, 125]
    assert stop['custody_verified_before_stop'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == VM_ID and not stop['other_vm_modified']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == '29A942FBF1594E1C09EC34ECE58DB02F1742E8B9FDCDA0E88B3084E3F4B7F192'
    qualified = check / 'qualified-native' / marker['run']
    native = json.loads((qualified / 'native-report.json').read_bytes())
    assert not native['full_original_A22_HC46_selected_native_gates_green']
    assert native['owned_error_headers'] == 8 and native['owned_warning_headers'] == [0, 0, 0, 0, 9, 0, 0]
    assert native['inherited_regression_headers'] == [0] * 7 and native['missing_objects'] == 31
    assert native['cache_objects_unchanged'] == 566 and native['bad_profiles'] == 172
    assert not (qualified / 'material-expanded-native-report.json').exists()
    paths = {ROOT / 'launch-once.json', Path(__file__).resolve()}
    paths.update(p for p in check.rglob('*') if p.is_file() and 'remote-evidence' not in p.parts)
    for name, handle, code in WRAPPERS:
        folder = ROOT / 'research-resume-20261011' / name
        command = json.loads((folder / 'command.json').read_bytes())
        assert command['native_exit'] == code
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == command[stream + '_sha256']
        if handle == 23769:
            assert 'RuntimeError: Added source object missing' in (folder / 'stderr').read_text(encoding='utf-8')
        paths.update(p for p in folder.iterdir() if p.is_file())
    with tarfile.open(custody['repository_path'], 'r:gz') as archive:
        members = archive.getmembers()
        assert len(members) == len({m.name for m in members}) == 80
        assert all(m.isfile() for m in members)
        for member in members:
            extracted = qualified / 'remote-evidence' / member.name
            assert extracted.read_bytes() == archive.extractfile(member).read()
        assert {m.name for m in members} == {p.relative_to(qualified / 'remote-evidence').as_posix() for p in (qualified / 'remote-evidence').rglob('*') if p.is_file()}
    total = sum(p.stat().st_size for p in paths)
    assert shutil.disk_usage(HERE).free - total >= 1536 * 1024**2
    out = HERE / 'full111-resume-failed-native-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    payload = out / 'complete-originals.tar.gz'
    with tarfile.open(payload, 'x:gz') as archive:
        for number, original in enumerate(sorted(paths)):
            name = f'{number:03d}-' + original.name
            pin = digest(original)
            archive.add(original, arcname=name, recursive=False)
            assert digest(original) == pin
            rows.append(dict(original=str(original), member=name, bytes=original.stat().st_size, sha256=pin))
    with tarfile.open(payload, 'r:gz') as archive:
        assert len(archive.getmembers()) == len(rows)
        for row in rows:
            data = archive.extractfile(row['member']).read()
            assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
    result = dict(schema='full111-complete-failed-native-stop-red-audit-custody-v1', files=rows,
        payload=dict(file=payload.name, bytes=payload.stat().st_size, sha256=digest(payload)),
        run=marker['run'], terminal_receipt=receipt, historical_independent_termination=stop, partial_red_audit=native,
        original_handles=dict(native=60064, stop=28272, audit=23769), original_exits=dict(native=1, stop=0, audit=1),
        original_audit_failure='Added source object missing', original_auditor_unmodified=True,
        native_archive_members=80, every_extracted_member_exactly_represented=True,
        original_progress_custody='a1cecd13:full111-native-progress-record-v1',
        exact_diagnostic_packet_custody='adf1e917:full111-native-diagnostic-packet-v2',
        complete_diagnostics_routed_to_disjoint_authors=True, no_native_acceptance=True, full_goal_complete=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(folder=str(out), complete_originals=len(rows), payload_bytes=payload.stat().st_size,
                         payload_sha256=digest(payload), original_failed_audit_preserved=True)), flush=True)


if __name__ == '__main__':
    main()
