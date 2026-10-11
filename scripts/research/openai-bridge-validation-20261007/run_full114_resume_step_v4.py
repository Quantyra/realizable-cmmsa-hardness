"""Preserve complete output from one explicitly selected continuation action."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import uuid
from custody_checks import digest
from full114_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
ALLOWED = {'refresh_full114_recovery_idle_v1.py', 'preserve_full114_recovery_v2.py', 'preserve_full114_recovery_v3.py', 'preserve_full114_recovery_v4.py', 'stage_full114_after_recovery_openssh_v2.py', 'run_full113_settled_cache_recovery_v1.py', 'terminate_full114_after_custody_openssh_v1.py', 'preserve_full114_frozen_package_v1.py', 'run_full114_native_openssh_v1.py', 'full114_postprocess.py', 'run_full114_cache_recovery_v2.py', 'inspect_full114_generated_cache_capacity_v1.py', 'audit_full114_cache_recovery_v2.py', 'inspect_full114_recovery_capacity_v2.py'}


def main():
    name, *args = sys.argv[1:]
    assert name in ALLOWED
    source = HERE / name
    folder = ROOT / 'research-resume-20261011' / (datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'-'+uuid.uuid4().hex[:12])
    folder.mkdir(parents=True, exist_ok=False)
    (folder / source.name).write_bytes(source.read_bytes())
    (folder / 'wrapper.snapshot.py').write_bytes(Path(__file__).read_bytes())
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
