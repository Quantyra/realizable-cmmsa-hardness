"""Reclaim local physical space losslessly from six settled trace logs."""
import json
from pathlib import Path
import shutil
import stat
import subprocess
from full109_builder02_controller import ROOT
from custody_checks import digest

SCOPES = [
    ('full100-matrix-fourier-bullet-repair-resource02', 'consumption-v2'),
    ('full103-spectral-owned-warning-repair-resource02', 'consumption-v2'),
    ('full89-resource02', 'consumption-v2'),
    ('full90-material-resource02', 'consumption-v1'),
    ('full95-manuscript-moment-syntax-repair-resource02', 'consumption-v1'),
    ('full97-spectral-bridge-utf8-section-repair-resource02', 'consumption-v1'),
]


def main():
    folder = ROOT/'local-custody-stdout-compression-v2'
    folder.mkdir(exist_ok=False)
    before_free = shutil.disk_usage(ROOT).free
    rows = []
    for number, (name, trace) in enumerate(SCOPES):
        path = ROOT.parent/name/trace/'qualification/probe.stdout'
        assert path.resolve().is_relative_to(ROOT.parent.resolve()) and path.is_file()
        assert not path.is_symlink()
        before = dict(bytes=path.stat().st_size, sha256=digest(path), attributes=path.stat().st_file_attributes)
        argv = ['compact.exe', '/C', '/Q', str(path)]
        result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        (folder/f'{number}.stdout').write_bytes(result.stdout)
        (folder/f'{number}.stderr').write_bytes(result.stderr)
        after = dict(bytes=path.stat().st_size, sha256=digest(path), attributes=path.stat().st_file_attributes)
        rows.append(dict(path=str(path), argv=argv, native_exit=result.returncode, before=before, after=after))
        (folder/'receipt.json').write_text(json.dumps(dict(files=rows, free_before_bytes=before_free,
            free_after_bytes=shutil.disk_usage(ROOT).free, deleted_files=False, compiler_invoked=False,
            VM_operation=False), indent=2)+'\n', encoding='utf-8')
        assert result.returncode == 0
        assert (before['bytes'], before['sha256']) == (after['bytes'], after['sha256'])
        assert after['attributes'] & stat.FILE_ATTRIBUTE_COMPRESSED
    print(json.dumps(dict(files=len(rows), before_free_bytes=before_free, after_free_bytes=shutil.disk_usage(ROOT).free,
                          all_logical_bytes_preserved=True)))


if __name__ == '__main__':
    main()
