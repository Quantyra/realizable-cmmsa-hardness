"""Losslessly compress exact committed working-tree text, excluding all dirty files."""
import ctypes
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def main():
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=REPO)
    head = git('rev-parse', 'HEAD').decode().strip()
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    rows = []
    dirty = set(git('diff', '--name-only', '-z').decode().split('\0')) | set(git('diff', '--cached', '--name-only', '-z').decode().split('\0'))
    for name in git('ls-files', '-z', '--', HERE.relative_to(REPO).as_posix()).decode().split('\0'):
        if not name or name in dirty:
            continue
        path = REPO / name
        if (path.suffix not in ('.json', '.jsonl', '.stdout', '.stderr', '.txt', '.log', '.patch', '.csv', '.stdin', '.py', '.lean', '.md') and path.name not in ('stdout','stderr')) or not path.is_file() or path.stat().st_size < 4096:
            continue
        assert path.resolve(strict=True).is_relative_to(HERE.resolve())
        high = ctypes.c_uint32(); low = allocated(str(path), ctypes.byref(high))
        assert low != 0xffffffff
        size = (high.value << 32) + low
        if size > path.stat().st_size * .8:
            rows.append(dict(path=str(path), relative=name, bytes=path.stat().st_size, sha256=digest(path), allocated_before=size))
    assert rows
    request = ''.join(head + ':' + row['relative'] + '\n' for row in rows).encode()
    native = subprocess.run(['git', 'cat-file', '--batch'], input=request, capture_output=True, cwd=REPO, check=True)
    raw = native.stdout; pos = 0; exact = []; differing = []
    for row in rows:
        end = raw.index(b'\n', pos); oid, kind, length = raw[pos:end].split(); n = int(length)
        assert kind == b'blob'
        body = raw[end+1:end+1+n]
        pos = end+1+n+1
        if n != row['bytes'] or body != Path(row['path']).read_bytes():
            differing.append(row); continue
        assert hashlib.sha256(body).hexdigest().upper() == row['sha256']
        row['git_blob'] = oid.decode(); exact.append(row)
    rows = exact
    assert rows
    assert pos == len(raw) and git('rev-parse', 'HEAD').decode().strip() == head
    out = HERE / 'full115-committed-text-lossless-v1'; out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (out / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    before = shutil.disk_usage(HERE).free
    (out / 'before.json').open('x').write(json.dumps(dict(head=head, files=rows, dirty_excluded=sorted(dirty), differing_raw_blobs_excluded=differing), indent=2)+'\n')
    commands = []
    for start in range(0, len(rows), 32):
        batch = rows[start:start+32]
        assert all(digest(row['path']) == row['sha256'] for row in batch)
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', *[row['path'] for row in batch]]
        child = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        for stream, data in [('stdout', child.stdout), ('stderr', child.stderr)]:
            (out / f'{start}.{stream}').open('xb').write(data)
        commands.append(dict(argv=argv, native_exit=child.returncode, stdout_sha256=digest(out/f'{start}.stdout'), stderr_sha256=digest(out/f'{start}.stderr')))
        (out / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n')
        assert child.returncode == 0 and all(digest(row['path']) == row['sha256'] for row in batch)
    assert git('rev-parse', 'HEAD').decode().strip() == head
    assert all(digest(row['path']) == row['sha256'] for row in rows)
    after = shutil.disk_usage(HERE).free
    result = dict(head=head, files=len(rows), free_before=before, free_after=after,
        all_logical_bytes_unchanged_and_exact_committed_blobs=True, all_dirty_and_untracked_files_excluded=True,
        no_git_metadata_changed=True, deleted_files=False, compiler_invoked=False)
    (out / 'result.json').open('x').write(json.dumps(result, indent=2)+'\n')
    assert after >= 1536*1024**2
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
