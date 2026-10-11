"""Audit and preserve the six original executions only after actual settlement."""
import json
from pathlib import Path
import shutil
from audit_full109_trace_cache_small_v1 import main as audit
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
HANDLES = {84:15395, 85:53812, 86:4494, 87:11662, 88:27916, 89:74386}


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    auditor = HERE/'audit_full109_trace_cache_small_v1.py'
    auditor_pin = digest(auditor)
    assert auditor_pin == '76A92A7C3E0D159D20A6FEEC2D2B43AFDA4235ADB15E7820B5A55E7BCB28C874'
    trace = ROOT/'consumption-v3'
    derivation = read(HERE/'full109-trace-small-cache-control-derivation-v1.json')
    paths = {Path(__file__).resolve(), auditor,
             trace/'pending-plans-revalidation-v2.json'}
    rows = []
    for number, handle in HANDLES.items():
        audit('receipt', number)
        scope = next(s for s in derivation['scopes'] if s['number'] == number)
        operations = [p for p in (trace/'cache-repoint-controls').glob('*/operation.json')
                      if read(p)['remote_control'] == scope['remote_control'] and read(p)['action'] == 'execute']
        assert len(operations) == 1
        operation_path = operations[0]
        operation = read(operation_path)
        commands = read(operation_path.parent/'commands.json')
        assert commands and all(c['native_exit'] == 0 for c in commands)
        name = f'run_full109_trace_cache_small_native{number}_v1.py'
        wrappers = [p for p in (ROOT/'research-resume-20261010').glob('*/command.json')
                    if Path(read(p)['argv'][-2]).name == name and read(p)['argv'][-1] == 'execute']
        assert len(wrappers) == 1
        wrapper_path = wrappers[0]
        wrapper = read(wrapper_path)
        assert wrapper['native_exit'] == 0
        for stream in ('stdout', 'stderr'):
            assert digest(wrapper_path.parent/stream) == wrapper[stream+'_sha256']
        current = trace/f'cache-small-receipt-audit-native{number}-v1.json'
        result = read(current)
        assert result['rows'] == 19233
        assert result['receipt_sha256'] == operation['result_sha256']
        rows.append(dict(number=number, original_tool_handle=handle, original_native_exit=0,
                         rows=result['rows'], receipt_sha256=result['receipt_sha256'],
                         plan_sha256=result['plan_sha256'], audit_sha256=digest(current),
                         disk_after_bytes=result['disk_after_bytes']))
        for folder in (operation_path.parent, wrapper_path.parent):
            paths.update(p for p in folder.rglob('*') if p.is_file())
        paths.add(current)
    assert digest(auditor) == auditor_pin and sum(r['rows'] for r in rows) == 115398
    prior = read(HERE/'full109-resume-checkpoint-v2-20261011T002456114472Z/index.json')
    preserved = {r['original']:r for r in prior['files']}
    for inspection in (ROOT/'trace-recovery-progress-v2').glob('*/inspection.json'):
        commands = read(inspection.parent/'commands.json')
        assert commands and all(c['native_exit'] == 0 for c in commands)
        for path in inspection.parent.rglob('*'):
            if path.is_file() and str(path) not in preserved:
                paths.add(path)
    byte_count = sum(p.stat().st_size for p in paths)
    assert shutil.disk_usage(ROOT).free - byte_count >= 1536*1024**2
    target = HERE/'full109-resume-recovery-settlement-v3'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    files = []
    for number, path in enumerate(sorted(paths)):
        data = path.read_bytes()
        destination = target/f'{number:03d}-{path.name}'
        destination.open('xb').write(data)
        pin = digest(destination)
        assert digest(path) == pin
        files.append(dict(original=str(path), copy=destination.name, bytes=len(data), sha256=pin))
    record = dict(schema='full109-six-original-trace-recovery-settlement-v3', scopes=rows,
                  files=files, total_rows=115398, complete_actual_plan_receipt_identity=True,
                  auditor_sha256=auditor_pin, inherited_originals_unstaged=True,
                  recovery_replayed=False, cloud_operation_invoked_by_this_audit=False,
                  trace_executed=False, fresh_remote_prelaunch_still_required=True,
                  accepted=False, full_goal_complete=False)
    (target/'index.json').open('x', encoding='utf-8').write(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), complete_original_files=len(files),
                          total_rows=115398, all_original_executions_native_exit=0,
                          free_bytes=shutil.disk_usage(ROOT).free, accepted=False)))


if __name__ == '__main__':
    main()
