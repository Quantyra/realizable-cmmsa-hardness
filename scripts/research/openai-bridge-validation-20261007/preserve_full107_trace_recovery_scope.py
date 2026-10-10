"""Preserve only a completed, independently audited sequential recovery scope."""
import hashlib
import json
from pathlib import Path
import sys
import subprocess
from audit_full107_trace_cache_recovery_v1_v4_v8 import ROOT, receipt_review

HERE = Path(__file__).parent


def verify_git(number):
    dest = HERE/f'full107-trace-recovery-record-v{number}'
    metadata = json.loads((dest/'preservation.json').read_bytes())
    repo = HERE.parents[2]
    paths = [f"HEAD:{(dest/row['preserved']).relative_to(repo).as_posix()}" for row in metadata['files']]
    result = subprocess.run(['git', 'cat-file', '--batch'], cwd=repo,
                            input=('\n'.join(paths)+'\n').encode(), capture_output=True, check=True)
    data = result.stdout
    offset = 0
    for row in metadata['files']:
        end = data.index(b'\n', offset)
        header = data[offset:end].split()
        assert header[1] == b'blob'
        size = int(header[2])
        body = data[end+1:end+1+size]
        assert size == row['bytes'] and hashlib.sha256(body).hexdigest().upper() == row['sha256']
        assert data[end+1+size:end+2+size] == b'\n'
        offset = end+2+size
    assert offset == len(data)
    print(json.dumps(dict(scope=number, committed_original_hashes_verified=len(paths))))


def main(number):
    assert number in (4, 5, 6, 7, 8)
    batch = ROOT/'remaining-recovery-batch'
    assert json.loads((batch/f'scope{number}.native-exit.json').read_bytes()) == {'native_exit': 0}
    receipt_review(number)
    audit_path = ROOT/f'trace-cache-receipt-audit-v{number}.json'
    audit = json.loads(audit_path.read_bytes())
    operation = Path(audit['operation']['local_result']).parent
    idle_lines = (batch/f'scope{number}.idle.stdout').read_text(encoding='utf-8').splitlines()
    idle = json.loads(idle_lines[-1])
    assert idle['refreshed']
    idle_folder = Path(idle['receipt']).parent
    dest = HERE/f'full107-trace-recovery-record-v{number}'
    dest.mkdir(exist_ok=True)
    rows = []

    def retain(source, relative):
        data = source.read_bytes()
        target = dest/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert target.read_bytes() == data, 'Preserved evidence drift'
        else:
            target.open('xb').write(data)
        rows.append(dict(source=str(source), preserved=relative,
                         bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper()))

    for folder, prefix in ((operation, 'transaction'), (idle_folder, 'idle')):
        for source in sorted(folder.rglob('*')):
            if source.is_file():
                retain(source, prefix+'/'+source.relative_to(folder).as_posix())
    retain(audit_path, audit_path.name)
    for suffix in ('command.json', 'native-exit.json', 'stdout', 'stderr', 'idle.stdout', 'idle.stderr'):
        source = batch/f'scope{number}.{suffix}'
        retain(source, 'batch/'+source.name)
    (dest/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof\n', encoding='utf-8')
    metadata = dict(scope=number, native_exit=0, complete_receipt_audited=True,
                    files=rows, disk_after_bytes=audit['disk_after_bytes'],
                    current_exact_duplicate_equality=True,
                    exhaustive_capture_time_cache_identity_claimed=False,
                    trace_invoked=False, accepted=False)
    data = (json.dumps(metadata, indent=2)+'\n').encode('utf-8')
    path = dest/'preservation.json'
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(dict(scope=number, preserved_files=len(rows), directory=str(dest))))


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '--verify-git':
        verify_git(int(sys.argv[2]))
    else:
        assert len(sys.argv) == 2
        main(int(sys.argv[1]))
