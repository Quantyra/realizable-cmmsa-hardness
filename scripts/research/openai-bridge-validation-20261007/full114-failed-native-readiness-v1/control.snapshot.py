"""Preserve complete failed native, guarded stop, and unchanged red audit originals."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest, verify_local_custody
from full114_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent
WRAPPERS = [('20261011T065854166238Z-8cecfbdd4661', 50327, 1),
            ('20261011T070935848425Z-938618016202', 7602, 0),
            ('20261011T071559885294Z-5e558ead0c97', 67155, 1),
            ('20261011T065506658900Z-d2b8df53deed', 56798, 0)]


def main(inventory_only=False):
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert marker['run'] == receipt['run'] == stop['run'] == 'cmmsa_a8_output_20261011T070000Z_135b1f28'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [r['native_exit'] for r in receipt['terminal']['stages']] == [0, 0, 0, 0, 1, 125, 125]
    assert stop['custody_verified_before_stop'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == VM_ID and not stop['other_vm_modified']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert custody['remote_sha256'] == 'F94CD8899B40E42802B5294EF4EFD0189F9584EBE8E1FAEABCC5826FED8A56A3'
    qualified = check / 'qualified-native' / marker['run']
    native = json.loads((qualified / 'native-report.json').read_bytes())
    assert not native['full_original_A22_HC46_selected_native_gates_green']
    assert native['owned_error_headers'] == 1 and native['owned_warning_headers'] == [0] * 7
    assert native['inherited_regression_headers'] == [0] * 7 and native['missing_objects'] == 29
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
        if handle == 67155:
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
    for observation in (ROOT/'live-native-inspections-v1').iterdir():
        assert (observation/'inspection.json').is_file()
        for record in json.loads((observation/'transport/commands.json').read_bytes()):
            assert record['native_exit'] == 0
            for stream in ('stdout','stderr'):
                assert digest(Path(record[stream+'_path'])) == record[stream+'_sha256']
        paths.update(p for p in observation.rglob('*') if p.is_file())
    idle = ROOT.parent / 'full113-exact-real-complex-operators-repair3-resource02/settled-cache-recovery-v1/idle-refresh-controls/20261011T065508310777Z'
    assert json.loads((idle/'idle-refreshed.json').read_bytes())['idle_timer_active']
    for command in json.loads((idle/'transport/commands.json').read_bytes()):
        assert command['native_exit'] == 0
        for stream in ('stdout', 'stderr'):
            assert digest(Path(command[stream+'_path'])) == command[stream+'_sha256']
    paths.update(p for p in idle.rglob('*') if p.is_file())
    total = sum(p.stat().st_size for p in paths)
    if inventory_only:
        out = HERE/'full114-failed-native-readiness-v1'
        out.mkdir(exist_ok=False)
        (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
        (out/'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
        rows = [dict(original=str(p), bytes=p.stat().st_size, sha256=digest(p)) for p in sorted(paths)]
        result = dict(files=rows, run=marker['run'], native_archive_sha256=custody['remote_sha256'],
            original_handles=dict(native=50327, stop=7602, audit=67155, idle=56798),
            original_exits=dict(native=1, stop=0, audit=1, idle=0), native_report=native,
            independent_termination=stop['independent'], total_logical_bytes=total,
            free_bytes=shutil.disk_usage(HERE).free, reserve_bytes=1536*1024**2,
            archive_created=False, complete_portable_custody=False, all_originals_retained=True,
            cleanup_authorization_received=False, files_deleted=False, compiler_invoked=False)
        (out/'index.json').open('x').write(json.dumps(result,indent=2)+'\n')
        print(json.dumps(dict(folder=str(out), originals=len(rows), total_logical_bytes=total,
            free_bytes=result['free_bytes'], archive_created=False)),flush=True)
        return
    assert shutil.disk_usage(HERE).free - total >= 1536 * 1024**2
    out = HERE / 'full114-resume-failed-native-v1'
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
    result = dict(schema='full114-complete-failed-native-stop-red-audit-custody-v1', files=rows,
        payload=dict(file=payload.name, bytes=payload.stat().st_size, sha256=digest(payload)),
        run=marker['run'], terminal_receipt=receipt, historical_independent_termination=stop, partial_red_audit=native,
        original_handles=dict(native=50327, stop=7602, audit=67155, idle=56798), original_exits=dict(native=1, stop=0, audit=1, idle=0),
        original_audit_failure='Added source object missing', original_auditor_unmodified=True,
        native_archive_members=80, every_extracted_member_exactly_represented=True,
        original_progress_custody='All three complete original Full114 observations and additional settled idle refresh transport streams are included here',
        exact_diagnostic_packet_custody='e0b53e9b:full114-native-diagnostic-packet-v1',
        complete_diagnostics_routed_to_disjoint_authors=True, no_native_acceptance=True, full_goal_complete=False)
    (out / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(folder=str(out), complete_originals=len(rows), payload_bytes=payload.stat().st_size,
                         payload_sha256=digest(payload), original_failed_audit_preserved=True)), flush=True)


if __name__ == '__main__':
    main()
