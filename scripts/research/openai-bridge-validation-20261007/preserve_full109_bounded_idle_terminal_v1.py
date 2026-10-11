"""Preserve the original bounded keeper's actual terminal; no new remote operation."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('C:/Users/dfred/.quantyra/builder02/full109-exact-crosslevel-warning-repair-resource02')
WRAPPER = ROOT / 'research-resume-20261010/20261011T001639692236Z'
REMOTE = ROOT / 'trace-staging-idle-lease-v1/20261011T001648918869Z'
SOURCE_PIN = 'CE0755DDC5A2AFA36F508F7BA54049BBEEF8319A46F3ABA04648A8274C1777CD'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    command = json.loads((WRAPPER / 'command.json').read_bytes())
    assert command['pid'] == 18936 and command['source_sha256'] == SOURCE_PIN
    assert command['native_exit'] in (0, 1), 'Original keeper has no authoritative terminal'
    assert command['finished_utc']
    assert sha((WRAPPER / 'maintain_full109_trace_staging_idle_lease_v1.py').read_bytes()) == SOURCE_PIN
    for stream in ('stdout', 'stderr'):
        assert sha((WRAPPER / stream).read_bytes()) == command[stream + '_sha256']
    commands = json.loads((REMOTE / 'commands.json').read_bytes())
    assert commands[0]['native_exit'] == 0
    for i, receipt in enumerate(commands):
        for stream in ('stdout', 'stderr'):
            assert sha((REMOTE / f'{i}.{stream}').read_bytes()) == receipt[stream + '_sha256']
    result = None
    if command['native_exit'] == 0:
        assert len(commands) == 2 and all(row['native_exit'] == 0 for row in commands)
        result = json.loads((REMOTE / 'inspection.json').read_bytes())
        assert result == json.loads((REMOTE / '1.stdout').read_bytes())
        assert result['maximum_seconds'] == 3600
        assert result['timer_disabled'] is result['compiler_invoked'] is result['vm_power_operation'] is False
        assert result['refresh_epochs'] == sorted(set(result['refresh_epochs']))
        assert 1 <= len(result['refresh_epochs']) <= 60
    contents = {}
    for label, folder in [('wrapper', WRAPPER), ('remote', REMOTE)]:
        for path in sorted(folder.rglob('*')):
            if path.is_file():
                assert path.resolve().is_relative_to(folder.resolve())
                rel = label + '/' + path.relative_to(folder).as_posix()
                contents[rel] = (path, path.read_bytes())
    target = HERE / 'full109-bounded-idle-terminal-record-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for rel, (original, data) in contents.items():
        dest = target / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.open('xb').write(data)
        assert dest.read_bytes() == original.read_bytes() == data
        rows.append(dict(original=str(original), copy=rel, bytes=len(data), sha256=sha(data)))
    record = dict(original_handle=93592, original_pid=18936,
                  native_exit=command['native_exit'], finished_utc=command['finished_utc'],
                  files=rows, successful_remote_inspection=result,
                  keeper_replayed=False, vm_status_now_independently_known=False,
                  fresh_authenticated_vm_inspection_still_required=True,
                  trace_launched=False, lean_executed_by_this_action=False,
                  cloud_operation_by_this_action=False, full_goal_complete=False)
    (target / 'index.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(dict(files=len(rows), native_exit=command['native_exit'],
                          refresh_count=len(result['refresh_epochs']) if result else None,
                          vm_status_now_independently_known=False)))


if __name__ == '__main__':
    main()
