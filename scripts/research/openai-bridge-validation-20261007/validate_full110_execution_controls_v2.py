"""Preserve complete offline control checks and synthetic test outputs; no GCP/Lean."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import uuid

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    folder = HERE / ('full110-execution-control-validation-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + uuid.uuid4().hex[:8])
    folder.mkdir()
    (folder / '.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    derivation = json.loads((HERE / 'full110-execution-control-derivation-v1.json').read_bytes())
    paths = [HERE / row['target'] for row in derivation['records']]
    paths += [HERE / name for name in ('derive_full110_execution_controls.py', 'full110_capture_gates.py',
              'test_full110_full_scope_terminal.py', 'validate_full110_execution_controls_v2.py',
              'full110-execution-control-derivation-v1.json')]
    snapshots = []
    for path in paths:
        data = path.read_bytes()
        if path.suffix == '.py':
            ast.parse(data.decode('utf-8'), filename=path.name)
        (folder / path.name).open('xb').write(data)
        snapshots.append(dict(original=str(path), copy=path.name, bytes=len(data), sha256=sha(data)))
    records = []
    commands = [[sys.executable, '-B', '-X', 'utf8', '-c', "import sys;sys.path.insert(0,'.');import full110_capture_gates as task;task.validate_successor()"],
                [sys.executable, '-B', '-X', 'utf8', '-c',
                 "import sys,unittest;sys.path.insert(0,'.');unittest.main(module=None,argv=['unittest','-v','test_full110_terminal','test_full110_full_scope_terminal'])"]]
    for i, argv in enumerate(commands):
        record = dict(argv=argv, started_utc=datetime.now(timezone.utc).isoformat())
        with (folder / (str(i) + '.stdout')).open('xb') as out, (folder / (str(i) + '.stderr')).open('xb') as err:
            process = subprocess.Popen(argv, cwd=HERE, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
            record['pid'] = process.pid
            records.append(record)
            (folder / 'commands.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
            while True:
                try:
                    native = process.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    print(json.dumps(dict(folder=str(folder), original_pid=process.pid, still_running=True)), flush=True)
        record.update(native_exit=native, finished_utc=datetime.now(timezone.utc).isoformat(),
                      stdout_sha256=sha((folder / (str(i) + '.stdout')).read_bytes()),
                      stderr_sha256=sha((folder / (str(i) + '.stderr')).read_bytes()))
        (folder / 'commands.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
        if native:
            break
    for row in snapshots:
        assert Path(row['original']).read_bytes() == (folder / row['copy']).read_bytes()
    passed = len(records) == len(commands) and all(row.get('native_exit') == 0 for row in records)
    result = dict(files=snapshots, all_offline_checks_passed=passed,
                  python_syntax_passed=True, test_evidence_is_synthetic_not_native=True,
                  cloud_operation=False, lean_executed=False, launch_clearance=False,
                  native_verified=False, accepted=False, full_goal_complete=False)
    (folder / 'result.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), all_offline_checks_passed=passed,
                          command_native_exits=[row.get('native_exit') for row in records],
                          cloud_operation=False, native_verified=False)), flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
