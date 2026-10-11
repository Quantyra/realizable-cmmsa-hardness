"""Preserve complete output from one explicitly selected continuation action."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import uuid
from custody_checks import digest
from full116_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
ALLOWED = {'prepare_full117_extracted_package_cleanup_plan_v1.py', 'preserve_full116_native_phase_v2.py', 'compress_full116_settled_text_v1.py', 'prepare_numeric_full_closure_inventory_v2.py', 'prepare_numeric_full_closure_inventory_v1.py', 'inspect_full116_native_progress_v1.py', 'preserve_full116_native_phase_v1.py', 'preserve_full116_staging_success_v1.py', 'stage_full116_openssh_v2.py', 'run_full116_cache_recovery_v1.py', 'audit_full116_cache_recovery_v1.py', 'preserve_full116_recovery_v1.py', 'derive_full116_cache_recovery_v1.py', 'stage_full116_openssh_v1.py', 'inspect_full116_recovery_capacity_v1.py', 'inspect_full116_generated_cache_capacity_v1.py', 'inspect_full116_generated_cache_capacity_v2.py', 'run_full116_native_openssh_v1.py', 'terminate_full116_after_custody_openssh_v1.py', 'full116_postprocess.py', 'full116_capture_gates.py', 'validate_full116_execution_controls_v2.py'}


def main():
    name, *args = sys.argv[1:]
    assert name in ALLOWED
    source = HERE / name
    folder = ROOT / 'research-resume-20261011' / (datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'-'+uuid.uuid4().hex[:12])
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
    code = 'import runpy,sys;sys.path.insert(0,sys.argv[1]);import full115_cumulative_actual_receipts_v1 as a;a.activate();p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name="__main__")'
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
