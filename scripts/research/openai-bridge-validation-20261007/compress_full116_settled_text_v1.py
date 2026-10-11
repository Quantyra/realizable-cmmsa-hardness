"""Reversible NTFS compression of exact settled evidence text; never deletes files."""
import ctypes
from ctypes import wintypes
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
BASE = Path('C:/Users/dfred/.quantyra/builder02').resolve(strict=True)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def allocated(path):
    function = ctypes.windll.kernel32.GetCompressedFileSizeW
    function.argtypes = [wintypes.LPCWSTR, ctypes.POINTER(wintypes.DWORD)]
    function.restype = wintypes.DWORD
    high = wintypes.DWORD()
    low = function(str(path), ctypes.byref(high))
    assert low != 0xffffffff
    return (high.value << 32) | low


def main():
    paths = []; parents = []
    for number in (115, 116):
        root, = BASE.glob('full' + str(number) + '-exact-real-complex-operators-*resource02')
        marker = json.loads((root / 'launch-once.json').read_bytes())
        check = Path(marker['preflight']).resolve(strict=True)
        assert check.is_relative_to(root.resolve())
        terminal = json.loads((check / 'terminal-custody.json').read_bytes())
        stopped = json.loads((check / 'vm-termination.json').read_bytes())
        assert marker['run'] == terminal['run'] == stopped['run']
        assert terminal['terminal']['native_terminal'] and stopped['custody_verified_before_stop']
        assert stopped['independent']['status'] == 'TERMINATED'
        assert str(stopped['independent']['id']) == '7237681467779354904'
        parents.append(dict(number=number, terminal_sha256=digest(check / 'terminal-custody.json'),
                            stop_sha256=digest(check / 'vm-termination.json')))
        for directory in (check / 'qualified-native', check / 'executed-controls'):
            for path in directory.rglob('*'):
                if not path.is_file() or path.is_symlink():
                    continue
                if directory.name == 'qualified-native' and 'remote-evidence' not in path.parts:
                    continue
                if path.suffix.lower() not in ('.lean', '.json', '.py', '.md', '.stdout', '.stderr', '.native-exit', '.txt'):
                    continue
                resolved = path.resolve(strict=True)
                assert resolved == path.absolute() and resolved.is_relative_to(check)
                assert not any(p.is_symlink() for p in [path, *path.parents] if p.is_relative_to(BASE))
                paths.append(resolved)
    assert paths and len(set(paths)) == len(paths) and len(paths) <= 250
    rows = [dict(path=str(p), bytes=p.stat().st_size, sha256=digest(p), allocated_before=allocated(p)) for p in sorted(paths)]
    assert sum(row['bytes'] for row in rows) < 50 * 1024**2
    folder = HERE / ('full116-settled-text-compression-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_bytes(b'* -text\n')
    (folder / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    (folder / 'plan.json').write_bytes((json.dumps(dict(files=rows, parents=parents, prior_root_authorization='Reversible filesystem compression of exact preserved text; hashes before and after; bounded settled scope excludes live sources/workspaces', files_deleted=False), indent=2) + '\n').encode())
    before = shutil.disk_usage(BASE).free
    commands = []
    for offset in range(0, len(rows), 16):
        group = rows[offset:offset + 16]
        for row in group:
            assert digest(Path(row['path'])) == row['sha256']
        argv = ['C:/Windows/System32/compact.exe', '/C', '/I', '/Q', *[row['path'] for row in group]]
        result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        name = str(len(commands))
        (folder / (name + '.stdout')).write_bytes(result.stdout)
        (folder / (name + '.stderr')).write_bytes(result.stderr)
        commands.append(dict(argv=argv, native_exit=result.returncode,
                             stdout_sha256=digest(folder / (name + '.stdout')),
                             stderr_sha256=digest(folder / (name + '.stderr'))))
        assert result.returncode == 0
    for row in rows:
        path = Path(row['path'])
        assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
        row['allocated_after'] = allocated(path)
    value = dict(files=rows, parents=parents, commands=commands, free_before=before,
                 free_after=shutil.disk_usage(BASE).free, all_byte_hashes_unchanged=True,
                 files_deleted=False, archives_replaced=False, live_sources_changed=False,
                 compiler_invoked=False, cloud_operation=False,
                 reversible_with_compact_uncompress=True)
    (folder / 'receipt.json').write_bytes((json.dumps(value, indent=2) + '\n').encode())
    print(json.dumps(dict(folder=str(folder), files=len(rows), reclaimed_allocated_bytes=sum(r['allocated_before'] - r['allocated_after'] for r in rows), free_after=value['free_after'])), flush=True)


if __name__ == '__main__':
    main()
