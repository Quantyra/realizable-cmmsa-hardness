"""Audit existing scope8 receipt without replaying a disconnected transaction."""
import hashlib
import json
from pathlib import Path
from audit_full107_trace_cache_recovery_v1_v4_v8 import ROOT, HERE, operation, plan_review
from custody_checks import digest


def read(path):
    return json.loads(path.read_bytes())


def main():
    assert not (ROOT/'launch-once.json').exists()
    plan_review()
    plan_op = operation(8, 'plan')
    collected = operation(8, 'collect-receipt')
    assert collected['control_sha256'] == plan_op['control_sha256']
    assert collected['VM']['id'] == '7237681467779354904'
    failed = ROOT/'cache-repoint-controls/20261010T070839415312Z'
    assert digest(failed/'executed-repoint-control.py') == plan_op['control_sha256']
    commands = read(failed/'commands.json')
    assert len(commands) == 3
    assert all(row['native_exit'] == 0 for row in commands[:2])
    last = commands[-1]
    expected = '--command=python3 -B '+plan_op['remote_control']+'/full107_trace_cache_repoint_v8.py --execute'
    assert expected in last['argv'] and last['native_exit'] == 1 and not last['timed_out']
    assert 'Remote side unexpectedly closed network connection' in (failed/'control/002.stderr').read_text()
    batch = ROOT/'remaining-recovery-batch'
    terminal = read(batch/'batch-terminal.json')
    assert terminal == dict(completed_scopes=[4,5,6,7], failure='Scope8 failed with native exit1; retain original receipts', probe_invoked=False, VM_power_operation=False)
    assert read(batch/'scope8.native-exit.json') == {'native_exit': 1}
    plan = read(Path(plan_op['local_result']))
    receipt = read(Path(collected['local_result']))
    assert receipt['applied'] == plan['rows'] and len(receipt['applied']) == 19233
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for key in ('warm_files_written', 'source_or_project_object_files_changed', 'failed_evidence_archive_changed', 'compiler_invoked'):
        assert receipt[key] is False
    assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
    result = dict(scope=8, failed_transport_native_exit=1, original_batch_native_exit=1,
                  complete_existing_receipt_collected=True, operation=collected,
                  rows=19233, disk_after_bytes=receipt['disk_after_bytes'],
                  content_and_reversibility_preserved=True, transaction_replayed=False,
                  original_failure_reclassified=False, trace_invoked=False, accepted=False)
    dest = HERE/'full107-trace-recovery-record-v8'
    dest.mkdir(exist_ok=True)
    rows = []

    def retain(source, relative):
        data = source.read_bytes()
        target = dest/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert target.read_bytes() == data
        else:
            target.open('xb').write(data)
        rows.append(dict(source=str(source), preserved=relative, bytes=len(data),
                         sha256=hashlib.sha256(data).hexdigest().upper()))

    idle = Path(json.loads((batch/'scope8.idle.stdout').read_text().splitlines()[-1])['receipt']).parent
    for folder, prefix in ((failed, 'failed-transport'), (Path(collected['local_result']).parent, 'collection'), (idle, 'idle')):
        for path in sorted(folder.rglob('*')):
            if path.is_file():
                retain(path, prefix+'/'+path.relative_to(folder).as_posix())
    for name in ['batch-once.json', 'batch-terminal.json']+[f'scope8.{suffix}' for suffix in ('command.json','native-exit.json','stdout','stderr','idle.stdout','idle.stderr')]:
        retain(batch/name, 'batch/'+name)
    (dest/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n')
    for path, value in ((dest/'audit.json', result), (dest/'preservation.json', dict(**result, files=rows))):
        data = (json.dumps(value, indent=2)+'\n').encode()
        if path.exists():
            assert path.read_bytes() == data
        else:
            path.open('xb').write(data)
    print(json.dumps(dict(**result, preserved_original_files=len(rows))))


if __name__ == '__main__':
    main()
