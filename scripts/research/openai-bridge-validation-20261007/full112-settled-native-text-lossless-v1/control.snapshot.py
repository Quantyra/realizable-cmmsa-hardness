"""Compress remaining settled native text only after exact archived-byte checks."""
import ctypes
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
from custody_checks import digest

HERE = Path(__file__).resolve().parent
BASE = Path('C:/Users/dfred/.quantyra/builder02')


def main():
    allocated = ctypes.windll.kernel32.GetCompressedFileSizeW
    allocated.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_uint32)]
    allocated.restype = ctypes.c_uint32
    candidates, resources = [], []
    for root in sorted(BASE.iterdir()):
        match = re.match(r'^full(\d+)-', root.name)
        if not root.is_dir() or not match or not 90 <= int(match[1]) <= 111:
            continue
        if not (root / 'launch-once.json').exists():
            continue
        marker = json.loads((root / 'launch-once.json').read_bytes())
        check = Path(marker['preflight']).resolve(strict=True)
        assert check.is_relative_to(root.resolve())
        receipt = json.loads((check / 'terminal-custody.json').read_bytes())
        stop = json.loads((check / 'vm-termination.json').read_bytes())
        assert marker['run'] == receipt['run'] == stop['run']
        assert receipt['terminal']['native_terminal'] and stop['independent']['status'] == 'TERMINATED'
        assert str(stop['independent']['id']) == '7237681467779354904'
        native = check / 'qualified-native' / marker['run'] / 'remote-evidence'
        if not native.exists():
            continue
        paths = []
        for path in native.iterdir():
            if not path.is_file() or path.suffix not in ('.json', '.patch', '.stdout') or path.stat().st_size < 250000:
                continue
            high = ctypes.c_uint32()
            low = allocated(str(path), ctypes.byref(high))
            assert low != 0xffffffff
            size = (high.value << 32) + low
            if size > path.stat().st_size * 0.8:
                paths.append((size, path))
        if not paths:
            continue
        archive_path = Path(receipt['custody']['repository_path'])
        assert digest(archive_path) == receipt['custody']['remote_sha256']
        with tarfile.open(archive_path, 'r:gz') as archive:
            for size, path in paths:
                assert path.resolve(strict=True).is_relative_to(native.resolve())
                data = path.read_bytes()
                assert data == archive.extractfile(path.name).read()
                candidates.append(dict(path=str(path), bytes=len(data), sha256=hashlib.sha256(data).hexdigest().upper(),
                    allocated_before=size, archive=str(archive_path), archive_sha256=receipt['custody']['remote_sha256'], member=path.name))
        resources.append(dict(root=str(root), historical_stop_sha256=digest(check / 'vm-termination.json')))
    selected = sorted(candidates, key=lambda row: row['allocated_before'], reverse=True)[:120]
    out = HERE / 'full112-settled-native-text-lossless-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (out / 'control.snapshot.py').open('xb').write(Path(__file__).read_bytes())
    (out / 'before.json').open('x', encoding='utf-8').write(json.dumps(dict(files=selected, resources=resources), indent=2) + '\n')
    free_before = shutil.disk_usage(BASE).free
    commands = []
    for number, row in enumerate(selected):
        path = Path(row['path'])
        assert digest(path) == row['sha256']
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(path)]
        result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        for stream, data in (('stdout', result.stdout), ('stderr', result.stderr)):
            (out / f'{number}.{stream}').open('xb').write(data)
        commands.append(dict(argv=argv, native_exit=result.returncode,
            stdout_sha256=digest(out / f'{number}.stdout'), stderr_sha256=digest(out / f'{number}.stderr')))
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n', encoding='utf-8')
        assert result.returncode == 0
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
    for row in selected:
        path = Path(row['path'])
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
    free_after = shutil.disk_usage(BASE).free
    value = dict(files=selected, free_before=free_before, free_after=free_after,
        every_file_matched_original_verified_native_archive=True, every_logical_size_and_sha_unchanged=True,
        no_files_deleted=True, no_source_or_git_or_cloud_operation=True,
        historical_termination_does_not_claim_current_VM_state=True, compiler_invoked=False)
    (out / 'result.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2) + '\n')
    assert free_after >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(out), files=len(selected), free_before=free_before, free_after=free_after)), flush=True)


if __name__ == '__main__':
    main()
