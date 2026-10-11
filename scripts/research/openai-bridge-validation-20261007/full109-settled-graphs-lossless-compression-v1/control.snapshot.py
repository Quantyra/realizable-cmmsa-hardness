"""Lossless Windows LZX storage for terminal graph evidence; no deletion or compiler."""
import json
from pathlib import Path
import shutil
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
BASE = Path('C:/Users/dfred/.quantyra/builder02')


def main():
    targets = []
    for name in ('full107-exact-product-energy-repair-resource02',
                 'full109-exact-crosslevel-warning-repair-resource02'):
        trace = BASE / name / 'consumption-v3'
        marker = json.loads((trace / 'launch-once.json').read_bytes())
        check = Path(marker['preflight']).resolve(strict=True)
        assert check.is_relative_to((trace / 'checks').resolve(strict=True))
        stop = json.loads((check / 'vm-termination.json').read_bytes())
        assert stop['independent']['status'] == 'TERMINATED'
        summary = json.loads((trace / 'qualification/qualification-summary.json').read_bytes())
        assert summary['structural_trace_qualification'] and not any(summary['unresolved_by_graph'].values())
        for relative in ('graphs/validated-graphs.json', 'probe.stdout', 'type-dag-qualification.json'):
            target = (trace / 'qualification' / relative).resolve(strict=True)
            assert target.is_relative_to(BASE.resolve(strict=True))
            targets.append(target)
    before = {str(p): dict(bytes=p.stat().st_size, sha256=digest(p)) for p in targets}
    destination = HERE / 'full109-settled-graphs-lossless-compression-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    (destination / 'control.snapshot.py').write_bytes(Path(__file__).read_bytes())
    (destination / 'before.json').write_text(json.dumps(before, indent=2)+'\n', encoding='utf-8')
    free_before = shutil.disk_usage(BASE).free
    commands = []
    for number, target in enumerate(targets):
        argv = ['compact.exe', '/C', '/F', '/EXE:LZX', str(target)]
        child = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        (destination / f'{number}.stdout').write_bytes(child.stdout)
        (destination / f'{number}.stderr').write_bytes(child.stderr)
        commands.append(dict(argv=argv, native_exit=child.returncode))
        (destination / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
        assert child.returncode == 0
        assert dict(bytes=target.stat().st_size, sha256=digest(target)) == before[str(target)]
        print(json.dumps(dict(file=str(target), logical_bytes_unchanged=True)), flush=True)
    after = {str(p): dict(bytes=p.stat().st_size, sha256=digest(p)) for p in targets}
    assert before == after
    free_after = shutil.disk_usage(BASE).free
    result = dict(schema='full109-settled-graph-lossless-storage-v1', logical_files=before,
                  all_logical_sizes_and_hashes_unchanged=True, free_before=free_before, free_after=free_after,
                  local_reserve_satisfied=free_after >= 1536 * 1024**2,
                  no_files_deleted=True, compiler_invoked=False, settled_files_only=True)
    (destination / 'result.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
