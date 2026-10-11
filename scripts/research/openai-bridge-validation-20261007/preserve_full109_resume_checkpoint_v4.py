"""Preserve settled successes and distinct transport/authentication failures."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    previous = read(HERE/'full109-resume-checkpoint-v2-20261011T002456114472Z/index.json')
    already = {row['original']:row for row in previous['files']}
    paths = set()
    actions = []
    for command in (ROOT/'research-resume-20261010').glob('*/command.json'):
        row = read(command)
        if 'native_exit' not in row:
            continue
        for stream in ('stdout','stderr'):
            assert digest(command.parent/stream) == row[stream+'_sha256']
        actions.append(dict(command=str(command), native_exit=row['native_exit']))
        paths.update(p for p in command.parent.rglob('*') if p.is_file())
    operations = []
    for number in range(85, 89):
        audit = ROOT/'consumption-v3'/f'cache-small-receipt-audit-native{number}-v1.json'
        result = read(audit)
        assert result['rows'] == 19233 and result['all_actual_rows_match_prior_verified_byte_identities']
        matches = [p for p in (ROOT/'consumption-v3/cache-repoint-controls').glob('*/operation.json')
                   if read(p)['action'] == 'execute' and read(p)['remote_control'].endswith(f'native{number}-v1')]
        assert len(matches) == 1
        operation = read(matches[0])
        assert operation['result_sha256'] == result['receipt_sha256'] == digest(operation['local_result'])
        assert all(c['native_exit'] == 0 for c in read(matches[0].parent/'commands.json'))
        operations.append(dict(scope=number, original_native_exit=0, rows=19233, receipt_sha256=result['receipt_sha256']))
        paths.add(audit)
        paths.update(p for p in matches[0].parent.rglob('*') if p.is_file())
    failed = ROOT/'consumption-v3/cache-repoint-controls/20261011T001909531238Z'
    assert [c['native_exit'] for c in read(failed/'commands.json')] == [0,0,0,0,1]
    paths.update(p for p in failed.rglob('*') if p.is_file())
    for base in ('trace-recovery-progress-v2', 'readonly-receipt-native89-v1'):
        for command in (ROOT/base).glob('*/commands.json'):
            rows = read(command)
            assert rows and all('native_exit' in row for row in rows)
            paths.update(p for p in command.parent.rglob('*') if p.is_file())
    paths.update([HERE/'inspect_full109_trace_recovery_progress_v2.py', HERE/'collect_full109_native89_receipt_v1.py'])
    selected = []
    for path in sorted(paths):
        if str(path) in already:
            assert digest(path) == already[str(path)]['sha256']
        else:
            selected.append(path)
    assert shutil.disk_usage(ROOT).free - sum(p.stat().st_size for p in selected) >= 1536*1024**2
    target = HERE/'full109-resume-checkpoint-v4'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    files = []
    for number, source in enumerate(selected):
        data = source.read_bytes()
        destination = target/f'{number:03d}-{source.name}'
        destination.open('xb').write(data)
        pin = digest(destination)
        assert digest(source) == pin
        files.append(dict(original=str(source), copy=destination.name, bytes=len(data), sha256=pin))
    record = dict(files=files, complete_receipt_audits=operations, settled_actions=actions,
                  original_scope89_handle=74386, original_scope89_native_exit=1,
                  scope89_remote_execution_native_exit=0, scope89_receipt_collection_complete=False,
                  scope84_original_handle=15395, scope84_transport_terminal_not_yet_observed=True,
                  original_inspection_handle5810_native_exit=1, original_collector_handle6899_native_exit=1,
                  authentication_error='Interactive reauthentication required for dfredriksen@quantyra.org',
                  goal_remains_active=True, cloud_work_waits_for_authentication=True,
                  trace_executed=False, accepted=False, full_goal_complete=False,
                  limitations=['Live scope84 collector and idle keeper are excluded.',
                               'The all-six-native0 settlement control v3 remains unexecuted; its premise is no longer met.',
                               'Original successful execution and failed receipt transport remain distinct.'])
    (target/'index.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), complete_original_files=len(files), audited_rows=4*19233, accepted=False)))


if __name__ == '__main__':
    main()
