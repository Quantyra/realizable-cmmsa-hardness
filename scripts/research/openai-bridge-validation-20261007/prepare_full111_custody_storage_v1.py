"""Lossless settled-plan compression and inheritance for new custody artifacts."""
import json
from pathlib import Path
import shutil
import stat
import subprocess
from custody_checks import digest
from full111_builder02_controller import ROOT
from audit_full110_settled_cache_recovery_v1 import RECOVERY

HERE = Path(__file__).resolve().parent


def main():
    assert not (ROOT / 'launch-once.json').exists()
    record = HERE / 'full110-recovery-plans-record-v1'
    index = json.loads((record / 'index.json').read_bytes())
    assert index['original_exit'] == 0 and index['all_seven_plans_verified']
    paths = []
    for row in index['files']:
        if Path(row['original']).name.endswith('-plan.json'):
            original, copy = Path(row['original']), record / row['copy']
            assert digest(original) == digest(copy) == row['sha256']
            paths.extend([original, copy])
    assert len(paths) == 14 and len(set(paths)) == 14
    before = {str(path): dict(bytes=path.stat().st_size, sha256=digest(path)) for path in paths}
    existing = {str(path): dict(bytes=path.stat().st_size, sha256=digest(path))
                for target in (ROOT, RECOVERY) for path in target.iterdir() if path.is_file()}
    destination = HERE / 'full111-custody-storage-record-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').open('x', encoding='utf-8').write('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    (destination / 'control.snapshot.py').open('xb').write(Path(__file__).read_bytes())
    (destination / 'before.json').open('x', encoding='utf-8').write(json.dumps(dict(settled_plans=before, root_files=existing), indent=2)+'\n')
    free_before = shutil.disk_usage(ROOT).free
    commands = []

    def run(argv):
        number = len(commands)
        result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        out, err = destination / f'{number}.stdout', destination / f'{number}.stderr'
        out.open('xb').write(result.stdout)
        err.open('xb').write(result.stderr)
        commands.append(dict(argv=argv, native_exit=result.returncode, stdout_sha256=digest(out), stderr_sha256=digest(err)))
        (destination / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
        assert result.returncode == 0

    for path in paths:
        run(['compact.exe', '/C', '/F', '/EXE:LZX', str(path)])
        assert dict(bytes=path.stat().st_size, sha256=digest(path)) == before[str(path)]
    inheritance = []
    for target in (ROOT, RECOVERY):
        assert target.resolve(strict=True).is_relative_to(ROOT.parent.resolve())
        attrs = target.stat().st_file_attributes
        run(['compact.exe', '/C', '/Q', str(target)])
        after = target.stat().st_file_attributes
        assert after & stat.FILE_ATTRIBUTE_COMPRESSED
        inheritance.append(dict(directory=str(target), attributes_before=attrs, attributes_after=after,
                                recursive_operation=False, future_files_only=True))
    for path, row in {**before, **existing}.items():
        assert dict(bytes=Path(path).stat().st_size, sha256=digest(Path(path))) == row
    result = dict(settled_plans=before, root_files=existing, directory_inheritance=inheritance,
        all_logical_sizes_and_hashes_unchanged=True, free_before=free_before,
        free_after=shutil.disk_usage(ROOT).free, files_deleted=False, compiler_invoked=False, VM_operation=False)
    (destination / 'result.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    assert result['free_after'] >= 1536 * 1024**2
    print(json.dumps(dict(folder=str(destination), settled_plan_files=14, future_custody_directories=2,
                         free_before=free_before, free_after=result['free_after'])), flush=True)


if __name__ == '__main__':
    main()
