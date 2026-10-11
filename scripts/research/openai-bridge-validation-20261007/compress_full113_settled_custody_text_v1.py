"""Lossless physical compression of settled originals with exact committed custody."""
import ctypes
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = Path('C:/Users/dfred/.quantyra/builder02').resolve()
FOLDERS = ['full111-complete-recovery-record-v4', 'full111-recovery-plans-openssh-record-v5', 'full112-resume-failed-native-v1']


def main():
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=REPO)
    head = git('rev-parse', 'HEAD').decode().strip()
    assert head.startswith('c56efdcb')
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    selected = {}; custody = []
    for name in FOLDERS:
        folder = HERE / name
        index = folder / 'index.json'
        assert index.read_bytes() == git('cat-file', 'blob', head + ':' + index.relative_to(REPO).as_posix())
        value = json.loads(index.read_bytes())
        payload = value.get('payload')
        if payload:
            archive = folder / payload['file']; pin = payload['sha256']
            originals = value['files']
        else:
            archive = folder / value['files'][0]['copy']; pin = value['files'][0]['sha256']
            originals = value['originals']
        assert digest(archive) == pin
        assert archive.read_bytes() == git('cat-file', 'blob', head + ':' + archive.relative_to(REPO).as_posix())
        custody.append(dict(index=str(index), index_sha256=digest(index), archive=str(archive), archive_sha256=pin))
        with tarfile.open(archive, 'r:gz') as tar:
            for row in originals:
                path = Path(row['original'])
                if row['bytes'] < 128000 or path.suffix not in ('.json', '.jsonl', '.stdout', '.stderr', '.txt', '.log', '.patch', '.csv', '.stdin'):
                    continue
                assert path.resolve(strict=True).is_relative_to(BASE)
                assert not path.parts[len(BASE.parts)].startswith('full113')
                if str(path) in selected:
                    continue
                high = ctypes.c_uint32(); low = allocated(str(path), ctypes.byref(high))
                assert low != 0xffffffff
                size = (high.value << 32) + low
                if size <= row['bytes'] * .8:
                    continue
                raw = path.read_bytes()
                assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest().upper() == row['sha256']
                assert tar.extractfile(row['member']).read() == raw
                selected[str(path)] = dict(path=str(path), bytes=len(raw), sha256=row['sha256'], allocated_before=size,
                    custody_index=str(index), custody_index_sha256=digest(index), archive=str(archive), member=row['member'])
    assert selected and git('rev-parse', 'HEAD').decode().strip() == head
    target = HERE / 'full113-settled-custody-text-lossless-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    rows = list(selected.values())
    (target / 'before.json').open('x').write(json.dumps(dict(head=head, files=rows, custody=custody), indent=2) + '\n')
    before = shutil.disk_usage(HERE).free; commands = []
    for i, row in enumerate(rows):
        path = Path(row['path']); assert digest(path) == row['sha256']
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(path)]
        child = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        for stream, data in [('stdout', child.stdout), ('stderr', child.stderr)]:
            (target / f'{i}.{stream}').open('xb').write(data)
        commands.append(dict(argv=argv, native_exit=child.returncode,
            stdout_sha256=digest(target / f'{i}.stdout'), stderr_sha256=digest(target / f'{i}.stderr')))
        (target / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        assert child.returncode == 0 and digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    assert git('rev-parse', 'HEAD').decode().strip() == head
    for row in rows:
        assert digest(Path(row['path'])) == row['sha256']
    after = shutil.disk_usage(HERE).free
    report = dict(head=head, files=rows, custody=custody, free_before=before, free_after=after,
        all_logical_bytes_and_hashes_unchanged=True, original_committed_archive_members_exact=True,
        active_full113_excluded=True, files_deleted=False, cloud_action=False, compiler_invoked=False)
    (target / 'result.json').open('x').write(json.dumps(report, indent=2) + '\n')
    assert after >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(target), files=len(rows), free_before=before, free_after=after)), flush=True)


if __name__ == '__main__':
    main()
