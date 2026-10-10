"""Preserve completed audited cache operations; never run a cloud or recovery command."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from audit_full109_small_cache_recovery_v3_v8 import OUTPUT, main as audit_scope

HERE = Path(__file__).parent


def preserve(action, number, handle):
    assert action in ('plan', 'receipt') and number in range(3, 9)
    audit_scope(action, number)
    audit_path = OUTPUT/('storage-'+action+'-complete-audit-v'+str(number)+'.json')
    remote = '/home/dfredriksen_quantyra_org/full109-storage-cache-repoint-v'+str(number)
    op_action = 'plan' if action == 'plan' else 'execute'
    matches = []
    for path in (OUTPUT/'cache-repoint-controls').glob('*/operation.json'):
        op = json.loads(path.read_bytes())
        if op['remote_control'] == remote and op['action'] == op_action:
            matches.append(path.parent)
    assert len(matches) == 1
    folder = matches[0]
    commands = json.loads((folder/'commands.json').read_bytes())
    assert commands and all(row['native_exit'] == 0 for row in commands)
    dest = HERE/('full109-storage-'+action+'-record-v'+str(number))
    dest.mkdir(exist_ok=True)
    (dest/'.gitattributes').write_bytes(b'* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for i, source in enumerate([*sorted(p for p in folder.rglob('*') if p.is_file()), audit_path]):
        data = source.read_bytes()
        name = f'{i:03}-'+source.name
        target = dest/name
        if target.exists():
            assert target.read_bytes() == data, 'Preserved original artifact drift'
        else:
            target.open('xb').write(data)
        rows.append(dict(original=str(source), copy=name, bytes=len(data),
                         sha256=hashlib.sha256(data).hexdigest().upper()))
    metadata = dict(scope=number, action=action, original_tool_handle=handle,
                    tool_native_exit_observed=0, sdk_native_exits_verified=True,
                    full_scope_audit_verified=True, files=rows, accepted=False)
    path = dest/'preservation.json'
    data = (json.dumps(metadata, indent=2)+'\n').encode()
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(dict(scope=number, action=action, preserved=len(rows), directory=str(dest))))


def verify(action, number):
    repo = HERE.parents[2]
    dest = HERE/('full109-storage-'+action+'-record-v'+str(number))
    rows = json.loads((dest/'preservation.json').read_bytes())['files']
    proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=repo, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    for row in rows:
        rel = (dest/row['copy']).relative_to(repo).as_posix()
        proc.stdin.write(('HEAD:'+rel+'\n').encode()); proc.stdin.flush()
        header = proc.stdout.readline().split()
        assert header[1] == b'blob'
        data = proc.stdout.read(int(header[2]))
        assert proc.stdout.read(1) == b'\n'
        assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest().upper() == row['sha256']
    proc.stdin.close()
    assert proc.wait() == 0
    print(json.dumps(dict(scope=number, action=action, committed_original_hashes_verified=len(rows))))


if __name__ == '__main__':
    if sys.argv[1] == '--verify-git':
        verify(sys.argv[2], int(sys.argv[3]))
    else:
        preserve(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
