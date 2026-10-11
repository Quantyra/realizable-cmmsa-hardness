"""Preserve exact bytes while enabling NTFS compression for the settled audit."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
from custody_checks import digest, verify_local_custody
from full114_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    check = Path(marker['preflight']).resolve(strict=True)
    assert check.is_relative_to((ROOT / 'checks').resolve(strict=True))
    receipt = json.loads((check / 'terminal-custody.json').read_bytes())
    stop = json.loads((check / 'vm-termination.json').read_bytes())
    assert receipt['terminal']['native_terminal']
    assert stop['independent']['status'] == 'TERMINATED' and str(stop['independent']['id']) == VM_ID
    assert marker['run'] == stop['run'] == receipt['run']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    assert not (check / 'qualified-native').exists()
    before = {str(p): digest(p) for p in check.rglob('*') if p.is_file()}
    selected = []
    for scope in ('full112-exact-real-complex-operators-repair2-resource02',
                  'full113-exact-real-complex-operators-repair3-resource02', ROOT.name):
        root = ROOT.parent / scope
        archive = root / 'input-archive.tar.gz'
        path = root / 'capture-manifest.json'
        with tarfile.open(archive, 'r:gz') as tar:
            raw = tar.extractfile(path.name).read()
        assert path.read_bytes() == raw
        selected.append(dict(path=str(path), sha256=digest(path), bytes=len(raw),
                             retained_archive=str(archive), archive_sha256=digest(archive), member=path.name))
    out = HERE / 'full114-audit-storage-lossless-v1'
    out.mkdir(exist_ok=False)
    (out / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (out / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    free_before = shutil.disk_usage(HERE).free
    (out / 'before.json').write_text(json.dumps(dict(check=str(check), check_files=before, selected=selected,
                                                    free_before=free_before), indent=2) + '\n')
    commands = []
    for argv in [['compact.exe', '/C', '/F', '/EXE:LZX', row['path']] for row in selected] + [['compact.exe', '/C', str(check)]]:
        result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        i = len(commands)
        for stream in ('stdout', 'stderr'):
            (out / f'{i}.{stream}').write_bytes(getattr(result, stream))
        commands.append(dict(argv=argv, native_exit=result.returncode,
                             stdout_sha256=digest(out / f'{i}.stdout'), stderr_sha256=digest(out / f'{i}.stderr')))
        (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        assert result.returncode == 0
    assert check.stat().st_file_attributes & 0x800
    assert before == {str(p): digest(p) for p in check.rglob('*') if p.is_file()}
    for row in selected:
        assert digest(row['path']) == row['sha256'] and Path(row['path']).stat().st_size == row['bytes']
    free_after = shutil.disk_usage(HERE).free
    with tarfile.open(custody['repository_path'], 'r:gz') as tar:
        extraction_bytes = sum(m.size for m in tar.getmembers())
    result = dict(free_before=free_before, free_after=free_after, extraction_logical_bytes=extraction_bytes,
                  check_directory_inherits_compression=True, all_logical_bytes_unchanged=True,
                  no_files_deleted=True, no_cloud_action=True, compiler_invoked=False,
                  reserve_bytes=1536 * 1024**2, minimum_overlay_allowance=2 * 1024**2)
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    assert free_after - extraction_bytes - 2 * 1024**2 >= 1536 * 1024**2
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
