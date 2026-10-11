"""Retain successful remote recovery separately from interrupted local custody transport."""
import json
from pathlib import Path
from audit_full109_trace_cache_small_v1 import main as audit
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
PIN = 'CA71F3017FFB28AD14A84DDE93230D576A70E27B3E3BD4EDEE545E38CAE84F47'


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    audit('plan', 84)
    original = ROOT/'consumption-v3/cache-repoint-controls/20261011T001721041630Z'
    wrapper = ROOT/'research-resume-20261010/20261011T001649934562Z'
    settlement = ROOT/'scope84-completed-download-settlement-v1'
    commands = read(original/'commands.json')
    assert [c['native_exit'] for c in commands] == [0,0,0,0,1]
    record = read(wrapper/'command.json')
    assert record['native_exit'] == 1
    for stream in ('stdout','stderr'):
        assert digest(wrapper/stream) == record[stream+'_sha256']
    intent = read(settlement/'intent.json')
    assert intent['pid'] == 15808 and intent['parent_pscp_pid'] == 4836
    assert intent['cancellation_requested'] and not intent['vm_power_operation']
    assert read(settlement/'taskkill.native-exit.json')['native_exit'] == 0
    assert digest(original/'receipt.json') == digest(settlement/'received-receipt.json') == PIN
    assert (original/'control/003.stdout').read_text().split()[0].upper() == PIN
    operations = [read(p) for p in (ROOT/'consumption-v3/cache-repoint-controls').glob('*/operation.json')]
    plan_op = next(p for p in operations if p['action'] == 'plan' and p['remote_control'].endswith('native84-v1'))
    plan = read(plan_op['local_result'])
    receipt = read(settlement/'received-receipt.json')
    assert receipt['applied'] == plan['rows'] and len(receipt['applied']) == 19233
    assert receipt['content_identity_verified_after_repoint'] and receipt['reversible_by_copying_identical_canonical_bytes']
    for key in ('warm_files_written','source_or_project_object_files_changed','failed_evidence_archive_changed','compiler_invoked'):
        assert receipt[key] is False
    assert receipt['disk_after_bytes'] > receipt['disk_before_bytes']
    result = dict(scope=84, rows=19233, original_tool_handle=15395, original_native_exit=1,
                  original_execution_command_native_exit=0, original_receipt_transport_native_exit=1,
                  original_failure_reclassified=False, settled_received_receipt_sha256=PIN,
                  plan_sha256=plan_op['result_sha256'], complete_actual_row_identity_verified=True,
                  only_verified_download_proxy_cancelled=True, active_TCP_absence_not_claimed=True,
                  disk_after_bytes=receipt['disk_after_bytes'], recovery_replayed=False,
                  trace_executed=False, fresh_remote_prelaunch_required=True, accepted=False)
    audit_path = ROOT/'consumption-v3/cache-small-received-receipt-audit-native84-v1.json'
    audit_path.open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    target = HERE/'full109-resume-native84-received-custody-v1'
    target.mkdir(exist_ok=False)
    (target/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n',encoding='utf-8')
    sources = {audit_path, HERE/'settle_full109_native84_completed_download_v1.py', Path(__file__).resolve()}
    for folder in (original, wrapper, settlement):
        sources.update(p for p in folder.rglob('*') if p.is_file())
    files = []
    for number, path in enumerate(sorted(sources)):
        data = path.read_bytes()
        name = f'{number:03d}-'+path.name
        (target/name).open('xb').write(data)
        assert digest(target/name) == digest(path)
        files.append(dict(original=str(path), copy=name, bytes=len(data), sha256=digest(path)))
    (target/'index.json').open('x',encoding='utf-8').write(json.dumps(dict(**result,files=files),indent=2)+'\n')
    print(json.dumps(dict(**result,complete_original_files=len(files))))


if __name__ == '__main__':
    main()
