"""Preserve full post-authentication transport failures, guarded boot, and receipt settlement."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
TRACE = ROOT / 'consumption-v3'


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    audit = TRACE / 'complete-trace-recovery-v4.json'
    result = read(audit)
    assert result['all115398_actual_rows_verified']
    assert result['original_scope84_and89_transport_native_exit1_retained']
    assert not result['original_recovery_replayed']
    assert not (TRACE / 'launch-once.json').exists()
    boot = TRACE / 'settled-cache-recovery-boot-v3'
    assert read(boot / 'boot-once.json')['before']['status'] == 'TERMINATED'
    assert read(boot / 'boot-result.json')['after']['status'] == 'RUNNING'
    paths = {audit, Path(__file__).resolve()}
    folders = [boot]
    for name in ('readonly-receipt-native89-v1', 'trace-recovery-progress-v2'):
        folders.extend(p for p in (ROOT / name).iterdir() if p.is_dir() and p.name.startswith('20261011T021'))
    actions = []
    for command in (ROOT / 'research-resume-20261010').glob('20261011T021*/command.json'):
        row = read(command)
        assert 'native_exit' in row, 'Retain live wrapper until native terminal'
        for stream in ('stdout', 'stderr'):
            assert digest(command.parent / stream) == row[stream + '_sha256']
        folders.append(command.parent)
        actions.append(dict(path=str(command), native_exit=row['native_exit']))
    for pattern in ('full109-auth-vm-recheck-20261011T021*', 'full109-ssh-transport-inspection-20261011T021*',
                    'full109-network-inspection-20261011T021*'):
        folders.extend(p for p in HERE.glob(pattern) if p.is_dir())
    for folder in folders:
        paths.update(p for p in folder.rglob('*') if p.is_file())
    names = ('inspect_full109_ssh_transport_v1.py', 'inspect_full109_network_state_v1.py',
             'derive_full109_postauth_resume_controls_v1.py', 'boot_full109_trace_recovery_v3.py',
             'run_full109_resume_step_v4.py', 'full109-postauth-resume-control-derivation-v1.json',
             'collect_full109_native89_receipt_v1.py', 'inspect_full109_trace_recovery_progress_v2.py',
             'audit_full109_complete_trace_recovery_v4.py')
    paths.update(HERE / name for name in names)
    assert shutil.disk_usage(ROOT).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    target = HERE / 'full109-resume-postauth-recovery-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    files = []
    for number, source in enumerate(sorted(paths)):
        data = source.read_bytes()
        destination = target / (f'{number:03d}-' + source.name)
        destination.open('xb').write(data)
        assert digest(source) == digest(destination)
        files.append(dict(original=str(source), copy=destination.name, bytes=len(data), sha256=digest(source)))
    observation = dict(tool25128_native_exit=1, tool12872_native_exit=1,
        collector_error='SSH native255: connection reset; IAP4010 destination read failed',
        progress_error='Owned IAP tunnel exited before connection; IAP4010 destination read failed',
        raw_internal_commands_preserved=True, complete_outer_stdout_stderr_not_claimed=True,
        exact_authenticated_transition='RUNNING, STOPPING, TERMINATED; then separately guarded start to RUNNING',
        guest_shutdown_log_utc='2026-10-11T02:14:09.754144881Z', shutdown_cause_unproven=True)
    value = dict(schema='full109-postauth-recovery-custody-v1', files=files, actions=actions,
                 original_tool_observations=observation, settlement=result,
                 trace_executed=False, fresh_remote_prelaunch_required=True, accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), complete_original_files=len(files), rows=115398,
                          index_sha256=digest(target / 'index.json'), accepted=False)))


if __name__ == '__main__':
    main()
