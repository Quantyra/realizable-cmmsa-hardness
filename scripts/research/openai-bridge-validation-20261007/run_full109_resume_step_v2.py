"""Preserve complete output from one explicitly selected continuation action."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
from custody_checks import digest
from full109_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
ALLOWED = {
    'boot_full109_trace_recovery_v2.py',
    'refresh_full109_trace_staging_idle_v1.py',
    'inspect_full109_trace_resources_v1.py',
    'audit_full109_trace_cache_small_v1.py',
    'audit_full109_trace_cache_large_v2.py',
    'audit_full109_pending_trace_plans_v2.py',
    'full109_consumption_v3_controller.py',
    'terminate_full109_consumption_v3.py',
    'qualify_full109_consumption_v3.py',
    'maintain_full109_trace_staging_idle_lease_v1.py',
} | {f'run_full109_trace_cache_small_native{n}_v1.py' for n in range(84, 90)}


def main():
    name, *args = sys.argv[1:]
    assert name in ALLOWED
    source = HERE / name
    folder = ROOT / 'research-resume-20261010' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    folder.mkdir(parents=True, exist_ok=False)
    (folder / source.name).write_bytes(source.read_bytes())
    code = 'import runpy,sys;sys.path.insert(0,sys.argv[1]);p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name="__main__")'
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
