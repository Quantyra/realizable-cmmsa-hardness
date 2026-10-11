"""Losslessly compress large committed evidence copies after exact HEAD byte checks."""
import ctypes
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'


def main():
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=REPO)

    head = git('rev-parse', 'HEAD').decode().strip()
    assert head.startswith('eca22c39')
    changed = set(git('diff', '--name-only', 'HEAD', '-z').decode().split('\0'))
    listed = git('ls-files', '-z', '--', PREFIX).decode().split('\0')
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    candidates = []
    for rel in listed:
        if not rel or rel in changed:
            continue
        path = REPO / rel
        first = path.relative_to(HERE).parts[0]
        if not first.startswith('full') or 'lossless' in first:
            continue
        if path.suffix not in ('.stdout', '.stderr', '.txt', '.patch', '.lean', '.md', '') or path.stat().st_size <= 128_000:
            continue
        high = ctypes.c_uint32()
        low = allocated(str(path), ctypes.byref(high))
        size = (high.value << 32) + low
        assert low != 0xffffffff
        if size > path.stat().st_size * 0.8:
            candidates.append((size, rel, path))
    selected = sorted(candidates, reverse=True)[:120]
    assert len(selected) >= 1
    rows = []
    for size, rel, path in selected:
        original = path.read_bytes()
        committed = git('show', head + ':' + rel)
        assert original == committed
        rows.append(dict(path=rel, bytes=len(original), sha256=hashlib.sha256(original).hexdigest().upper(),
                         allocated_before=size))
    target = HERE / 'full112-committed-text-lossless-v3'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (target / 'before.json').open('x', encoding='utf-8').write(json.dumps(dict(head=head, files=rows), indent=2)+'\n')
    free_before = shutil.disk_usage(HERE).free
    commands = []
    for number, row in enumerate(rows):
        path = REPO / row['path']
        assert digest(path) == row['sha256']
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(path)]
        result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        out, err = target / f'{number}.stdout', target / f'{number}.stderr'
        out.open('xb').write(result.stdout)
        err.open('xb').write(result.stderr)
        commands.append(dict(argv=argv, native_exit=result.returncode, stdout_sha256=digest(out), stderr_sha256=digest(err)))
        (target / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
        assert result.returncode == 0
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
    assert git('rev-parse', 'HEAD').decode().strip() == head
    for row in rows:
        path = REPO / row['path']
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    free_after = shutil.disk_usage(HERE).free
    value = dict(head=head, files=rows, free_before=free_before, free_after=free_after,
        exact_HEAD_bytes_verified_before=True, all_logical_sizes_and_hashes_unchanged=True,
        inherited_untracked_and_modified_files_excluded=True, files_deleted=False,
        compiler_invoked=False, VM_operation=False)
    (target / 'result.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    assert free_after >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(target), files=len(rows), free_before=free_before, free_after=free_after)), flush=True)


if __name__ == '__main__':
    main()
