"""Preserve complete output from one explicitly selected continuation action."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import uuid
from custody_checks import digest
from full118_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
ALLOWED = {'audit_full118_cache_recovery_v3.py','preserve_full118_recovery_v5.py','stage_full118_openssh_v5.py','preserve_full118_recovery_v4.py','stage_full118_openssh_v4.py','preserve_full118_recovery_v3.py','run_full118_cache_recovery_v3.py','stage_full118_openssh_v3.py','derive_full118_cache_recovery_v4.py','run_full118_cache_recovery_v2.py','audit_full118_cache_recovery_v2.py','preserve_full118_recovery_v2.py','stage_full118_openssh_v2.py','start_inspect_full118_owned_capacity_v3.py','prepare_builder02_full118.py','validate_full118_execution_controls_v1.py','derive_full118_cache_recovery_v2.py','inspect_full118_settled_capacity_v2.py','derive_full118_cache_recovery_v1.py','run_full118_cache_recovery_v1.py','audit_full118_cache_recovery_v1.py','preserve_full118_recovery_v1.py','stage_full118_openssh_v1.py','run_full118_native_openssh_v1.py','terminate_full118_after_custody_openssh_v1.py','full118_postprocess.py','full118_capture_gates.py'}


def main():
    name, *args = sys.argv[1:]
    assert name in ALLOWED
    source = HERE / name
    record_root = ROOT.parent/'full117-exact-real-complex-operators-repair7-resource02' if name=='prepare_builder02_full118.py' else ROOT
    folder = record_root / 'research-resume-20261011' / (datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'-'+uuid.uuid4().hex[:12])
    folder.mkdir(parents=True, exist_ok=False)
    (folder / source.name).write_bytes(source.read_bytes())
    (folder / 'wrapper.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (folder / 'authorized-custody-adapter.snapshot.py').write_bytes((HERE / 'full115_cumulative_cleanup_custody_v2.py').read_bytes())
    (folder / 'actual-receipt-binding.snapshot.py').write_bytes((HERE / 'full115_cumulative_actual_receipts_v1.py').read_bytes())
    additional = HERE / 'full115-authorized-additional18-cleanup-20261011T1931573414476Z'
    for receipt_name in ('approved-plan.json', 'receipt.json'):
        (folder / ('additional18-' + receipt_name)).write_bytes((additional / receipt_name).read_bytes())
    cleanup = HERE / 'full115-authorized-short-cleanup-20261011T1902419364615Z'
    for receipt_name in ('approved-plan.json', 'receipt.json'):
        (folder / receipt_name).write_bytes((cleanup / receipt_name).read_bytes())
    for n in ('plan.json','authorization.json','receipt.json'):
        (folder/('approved20-'+n)).write_bytes((HERE/'full117-approved20-extracted-cleanup-receipt-v1'/n).read_bytes())
    for n in ('full118_pending39_custody_v1.py','full118_authorized39_custody_v2.py'):
        (folder/n).write_bytes((HERE/n).read_bytes())
    for n in ('approved-plan.json','authorization.json','receipt.json'):
        (folder/('approved39-'+n)).write_bytes((HERE/'full118-approved39-cleanup-continuation-v2'/n).read_bytes())
    code = 'import runpy,sys;sys.path.insert(0,sys.argv[1]);import full118_authorized39_custody_v2 as a;a.activate();p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name="__main__")'
    argv = [sys.executable, '-B', '-X', 'utf8', '-c', code, str(HERE), str(source), *args]
    record = dict(argv=argv, source_sha256=digest(source), started_utc=datetime.now(timezone.utc).isoformat())
    with (folder / 'stdout').open('xb') as out, (folder / 'stderr').open('xb') as err:
        process = subprocess.Popen(argv, cwd=HERE, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
        record['pid'] = process.pid
        (folder / 'command.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
        print(json.dumps(dict(folder=str(folder), pid=process.pid, action=[name, *args])), flush=True)
        while True:
            try:
                result = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                print(json.dumps(dict(pid=process.pid, original_process_live=True)), flush=True)
    record.update(native_exit=result, finished_utc=datetime.now(timezone.utc).isoformat(),
                  stdout_sha256=digest(folder/'stdout'), stderr_sha256=digest(folder/'stderr'))
    (folder/'command.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), native_exit=result)), flush=True)
    raise SystemExit(result)


if __name__ == '__main__':
    main()
