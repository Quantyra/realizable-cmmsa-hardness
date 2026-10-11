"""Lossless physical compression of completed originals, checked against committed custody."""
import ctypes
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = Path('C:/Users/dfred/.quantyra/builder02').resolve()
FOLDERS = ['full112-resume-failed-native-v1', 'full113-resume-failed-native-v1',
           'full112-staging-success-record-v1', 'full113-staging-success-record-v1']


def main():
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=REPO)
    head = git('rev-parse', 'HEAD').decode().strip()
    assert head.startswith('91ea5a69')
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    selected = {}
    def consider(path, raw, custody):
        if len(raw) < 128000 or path.suffix not in ('.json', '.jsonl', '.stdout', '.stderr', '.txt', '.log', '.patch', '.csv', '.stdin'):
            return
        assert path.resolve(strict=True).is_relative_to(BASE)
        assert path.parts[len(BASE.parts)].startswith(('full112-', 'full113-'))
        if str(path) in selected:
            return
        assert path.read_bytes() == raw
        high = ctypes.c_uint32(); low = allocated(str(path), ctypes.byref(high))
        assert low != 0xffffffff
        size = (high.value << 32) + low
        if size <= len(raw) * .8:
            return
        selected[str(path)] = dict(path=str(path), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest().upper(), allocated_before=size, custody=custody)
    for name in FOLDERS:
        folder = HERE / name
        index = folder / 'index.json'
        assert index.read_bytes() == git('cat-file', 'blob', head + ':' + index.relative_to(REPO).as_posix())
        value = json.loads(index.read_bytes())
        payload = value.get('payload')
        if payload:
            archive = folder / payload['file']; pin = payload['sha256']; originals = value['files']
        else:
            archive = folder / value['files'][0]['copy']; pin = value['files'][0]['sha256']; originals = value['originals']
        assert digest(archive) == pin
        assert archive.read_bytes() == git('cat-file', 'blob', head + ':' + archive.relative_to(REPO).as_posix())
        with tarfile.open(archive, 'r:gz') as tar:
            for row in originals:
                path = Path(row['original'])
                raw = tar.extractfile(row['member']).read()
                assert len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest().upper() == row['sha256']
                custody = dict(index=str(index), index_sha256=digest(index), archive_sha256=pin, member=row['member'])
                consider(path, raw, custody)
                if name.endswith('failed-native-v1') and path.name.endswith('_evidence.tar.gz'):
                    assert path.read_bytes() == raw
                    run = path.name.removesuffix('_evidence.tar.gz')
                    extracted = path.parent / 'qualified-native' / run / 'remote-evidence'
                    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as native:
                        for member in native.getmembers():
                            if member.isfile():
                                p = extracted / member.name
                                assert p.resolve(strict=True).is_relative_to(extracted.resolve())
                                consider(p, native.extractfile(member).read(), dict(**custody, native_member=member.name))
    assert selected and git('rev-parse', 'HEAD').decode().strip() == head
    target = HERE / 'full114-settled-text-lossless-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (target / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    rows = list(selected.values())
    (target / 'before.json').open('x').write(json.dumps(dict(head=head, files=rows), indent=2) + '\n')
    before = shutil.disk_usage(HERE).free; commands = []
    for i, row in enumerate(rows):
        path = Path(row['path']); assert digest(path) == row['sha256']
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(path)]
        child = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        for stream, data in [('stdout', child.stdout), ('stderr', child.stderr)]:
            (target / f'{i}.{stream}').open('xb').write(data)
        commands.append(dict(argv=argv, native_exit=child.returncode, stdout_sha256=digest(target / f'{i}.stdout'), stderr_sha256=digest(target / f'{i}.stderr')))
        (target / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        assert child.returncode == 0 and digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
    assert git('rev-parse', 'HEAD').decode().strip() == head
    assert all(digest(Path(row['path'])) == row['sha256'] for row in rows)
    after = shutil.disk_usage(HERE).free
    result = dict(head=head, files=rows, free_before=before, free_after=after,
        all_logical_bytes_and_hashes_unchanged=True, original_committed_archive_members_exact=True,
        only_settled_112_113_touched=True, files_deleted=False, cloud_action=False, compiler_invoked=False)
    (target / 'result.json').open('x').write(json.dumps(result, indent=2) + '\n')
    assert after >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(target), files=len(rows), free_before=before, free_after=after)), flush=True)


if __name__ == '__main__':
    main()
