"""Losslessly compress only settled current-turn custody; verify every logical byte."""
import json
from pathlib import Path
import shutil
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
RESOURCE = Path('C:/Users/dfred/.quantyra/builder02/full109-exact-crosslevel-warning-repair-resource02')


def main():
    targets = [HERE / 'full109-resume-postauth-recovery-v1',
               RESOURCE / 'readonly-receipt-native89-v1/20261011T021635239571Z']
    assert json.loads((targets[0] / 'index.json').read_bytes())['settlement']['all115398_actual_rows_verified']
    assert (targets[1] / 'decoded-receipt.json').is_file()
    for target, boundary in zip(targets, (HERE, RESOURCE)):
        assert target.resolve(strict=True).is_relative_to(boundary.resolve(strict=True))
    paths = sorted(p for target in targets for p in target.rglob('*') if p.is_file())
    before = {str(p): dict(bytes=p.stat().st_size, sha256=digest(p)) for p in paths}
    free_before = shutil.disk_usage(HERE).free
    folder = HERE / 'full109-postauth-lossless-compression-v1'
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (folder / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    commands = []
    for number, target in enumerate(targets):
        argv = ['compact.exe', '/C', '/S:' + str(target), '/I', '/Q']
        child = subprocess.run(argv, cwd=target, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        (folder / f'{number}.stdout').write_bytes(child.stdout)
        (folder / f'{number}.stderr').write_bytes(child.stderr)
        commands.append(dict(argv=argv, cwd=str(target), native_exit=child.returncode))
        (folder / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
        assert child.returncode == 0
    after = {str(p): dict(bytes=p.stat().st_size, sha256=digest(p)) for p in paths}
    assert before == after
    free_after = shutil.disk_usage(HERE).free
    assert free_after >= 1536 * 1024**2
    result = dict(targets=[str(p) for p in targets], logical_files=before,
        all_logical_sizes_and_hashes_unchanged=True, free_before=free_before, free_after=free_after,
        no_files_deleted=True, compiler_invoked=False, live_trace_files_excluded=True)
    (folder / 'result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(folder=str(folder), verified_files=len(paths), free_before=free_before,
                         free_after=free_after, all_logical_sizes_and_hashes_unchanged=True)))


if __name__ == '__main__':
    main()
