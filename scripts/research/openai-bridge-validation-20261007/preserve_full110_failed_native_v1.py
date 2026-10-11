"""Preserve the original failed native run, guarded stop and partial red audit."""
import base64
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest, verify_local_custody
from full110_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent
WRAPPERS = [('20261011T025128622301Z-a98a1d6b5af1', 56715, 1),
            ('20261011T030126499890Z-6dc269da2ba2', 80335, 0),
            ('20261011T030621698435Z-015e8770fe21', 21673, 1)]


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert marker['run'] == receipt['run'] == stop['run'] == 'cmmsa_a8_output_20261011T025221Z_7046a7c0'
    assert receipt['terminal']['native_terminal'] and not receipt['terminal']['compile_green']
    assert [row['native_exit'] for row in receipt['terminal']['stages']] == [0, 0, 0, 0, 1, 125, 125]
    assert stop['custody_verified_before_stop'] and stop['independent']['status'] == 'TERMINATED'
    assert str(stop['independent']['id']) == VM_ID
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    qualified = check / 'qualified-native' / marker['run']
    native = json.loads((qualified / 'native-report.json').read_bytes())
    assert not native['full_original_A22_HC46_selected_native_gates_green']
    assert native['owned_error_headers'] == 6 and native['owned_warning_headers'] == [0, 0, 0, 0, 4, 0, 0]
    assert native['inherited_regression_headers'] == [0] * 7 and native['missing_objects'] == 32
    assert not (qualified / 'material-expanded-native-report.json').exists()
    paths = {ROOT / 'launch-once.json', Path(__file__).resolve()}
    paths.update(p for p in check.rglob('*') if p.is_file() and 'remote-evidence' not in p.parts)
    for name, handle, code in WRAPPERS:
        folder = ROOT / 'research-resume-20261011' / name
        command = json.loads((folder / 'command.json').read_bytes())
        assert command['native_exit'] == code
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == command[stream + '_sha256']
        paths.update(p for p in folder.iterdir() if p.is_file())
    observer = ROOT / 'live-native-inspections-v2/20261011T030027109362Z'
    observation = json.loads((observer / 'inspection.json').read_bytes())
    assert observation == json.loads((observer / '1.stdout').read_bytes())
    for number, row in enumerate(json.loads((observer / 'commands.json').read_bytes())):
        assert row['native_exit'] == 0
        for stream in ('stdout', 'stderr'):
            assert digest(observer / f'{number}.{stream}') == row[stream + '_sha256']
    for name, row in observation['streams'].items():
        path = observer / 'observed-streams' / name
        assert path.read_bytes() == base64.b64decode(row['base64'], validate=True)
        assert digest(path) == row['sha256']
    paths.update(p for p in observer.rglob('*') if p.is_file())
    with tarfile.open(custody['repository_path'], 'r:gz') as archive:
        names = []
        for member in archive:
            assert member.isfile() and member.name not in names
            names.append(member.name)
            extracted = qualified / 'remote-evidence' / member.name
            assert extracted.read_bytes() == archive.extractfile(member).read()
        assert len(names) == 80
        assert set(names) == {p.relative_to(qualified / 'remote-evidence').as_posix()
                             for p in (qualified / 'remote-evidence').rglob('*') if p.is_file()}
        assert archive.extractfile('stage-4.stdout').read() == (observer / 'observed-streams/stage-4.stdout').read_bytes()
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    destination = HERE / 'full110-resume-failed-native-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = destination / (f'{number:03d}-' + original.name)
        with original.open('rb') as source, copy.open('xb') as target:
            shutil.copyfileobj(source, target)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    result = dict(schema='full110-failed-native-stop-and-audit-custody-v1', files=rows, run=marker['run'],
        terminal_receipt=receipt, historical_independent_termination=stop, partial_red_audit=native,
        original_handles=dict(native=56715, stop=80335, audit=21673, progress=98460),
        original_exits=dict(native=1, stop=0, audit=1, progress=0),
        expanded_audit_failure='Added source object missing', original_auditor_unmodified=True,
        complete_archive_members=80, all_extracted_evidence_exactly_represented_in_archive=True,
        complete_diagnostics_routed_to_disjoint_authors=True, new_recovery_lifecycle_excluded=True,
        no_native_acceptance=True, full_goal_complete=False)
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), complete_original_files=len(rows),
        archive_sha256=custody['remote_sha256'], archive_bytes=custody['bytes'], original_failure_preserved=True)), flush=True)


if __name__ == '__main__':
    main()
