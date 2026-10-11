"""Losslessly compress settled native object inventories; preserve all logical bytes."""
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
from custody_checks import digest

HERE = Path(__file__).resolve().parent
BASE = Path('C:/Users/dfred/.quantyra/builder02')


def main():
    paths = []
    for number in (90, 91, 92, 95, 97, 100, 101, 102, 103, 105, 107, 108, 109, 110):
        resource, = BASE.glob('full' + str(number) + '-*')
        marker = json.loads((resource / 'launch-once.json').read_bytes())
        check = Path(marker['preflight'])
        stop = json.loads((check / 'vm-termination.json').read_bytes())
        receipt = json.loads((check / 'terminal-custody.json').read_bytes())
        assert marker['run'] == stop['run'] == receipt['run']
        assert receipt['terminal']['native_terminal'] and stop['independent']['status'] == 'TERMINATED'
        path = check / 'qualified-native' / marker['run'] / 'remote-evidence/package-object-before.json'
        assert path.resolve(strict=True).is_relative_to(BASE.resolve())
        with tarfile.open(receipt['custody']['repository_path'], 'r:gz') as archive:
            assert archive.extractfile('package-object-before.json').read() == path.read_bytes()
        paths.append(path)
    before = {str(p): dict(bytes=p.stat().st_size, sha256=digest(p)) for p in paths}
    destination = HERE / 'full110-settled-native-metadata-lossless-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (destination / 'control.snapshot.py').open('xb').write(Path(__file__).read_bytes())
    (destination / 'before.json').open('x', encoding='utf-8').write(json.dumps(before, indent=2)+'\n')
    free_before = shutil.disk_usage(BASE).free
    commands = []
    for number, path in enumerate(paths):
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(path)]
        child = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        (destination / f'{number}.stdout').open('xb').write(child.stdout)
        (destination / f'{number}.stderr').open('xb').write(child.stderr)
        commands.append(dict(argv=argv, native_exit=child.returncode))
        (destination / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
        assert child.returncode == 0
        assert dict(bytes=path.stat().st_size, sha256=digest(path)) == before[str(path)]
        print(json.dumps(dict(file=str(path), logical_bytes_unchanged=True)), flush=True)
    assert before == {str(p): dict(bytes=p.stat().st_size, sha256=digest(p)) for p in paths}
    free_after = shutil.disk_usage(BASE).free
    result = dict(files=before, free_before=free_before, free_after=free_after,
        every_file_matched_original_native_archive=True, all_logical_sizes_and_hashes_unchanged=True,
        no_files_deleted=True, compiler_invoked=False, local_reserve_satisfied=free_after >= 1536 * 1024**2)
    (destination / 'result.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), verified_files=len(paths), free_before=free_before, free_after=free_after)), flush=True)


if __name__ == '__main__':
    main()
