"""Preserve complete originals after the one seven-scope planner terminates."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full110_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
WRAPPER = ROOT / 'research-resume-20261011/20261011T030814924409Z-a74182a85f24'
PLANS = ROOT / 'settled-cache-recovery-v1/20261011T030858886970Z'
NUMBERS = [110, 90, 91, 92, 93, 94, 95]


def main():
    command = json.loads((WRAPPER / 'command.json').read_bytes())
    assert command['native_exit'] == 0 and command['pid'] == 15248
    assert command['argv'][-8:] == ['plan', *map(str, NUMBERS)]
    for stream in ('stdout', 'stderr'):
        assert digest(WRAPPER / stream) == command[stream + '_sha256']
    commands = json.loads((PLANS / 'commands.json').read_bytes())
    for row in commands:
        assert row['native_exit'] == 0 and not row['timed_out']
        for stream in ('stdout', 'stderr'):
            assert digest(PLANS / row[stream + '_path']) == row[stream + '_sha256']
    scopes = json.loads((HERE / 'full110-settled-cache-recovery-derivation-v1.json').read_bytes())['scopes']
    assert [row['number'] for row in scopes] == NUMBERS
    operations = []
    for scope in scopes:
        number = scope['number']
        record = json.loads((PLANS / f'operation-{number}.json').read_bytes())
        assert record['number'] == number and record['action'] == 'plan'
        assert record['helper_sha256'] == scope['helper_sha256'] == digest(PLANS / scope['helper'])
        path = PLANS / f'{number}-plan.json'
        assert Path(record['local_result']) == path and digest(path) == record['result_sha256']
        plan = json.loads(path.read_bytes())
        assert not plan['executed'] and not plan['compiler_invoked']
        assert plan['original_archive_sha256'] == scope['archive_sha256']
        assert sum(row['allocated_bytes'] for row in plan['rows']) == plan['allocated_bytes'] >= scope['target_bytes']
        operations.append(dict(number=number, plan_sha256=digest(path), rows=len(plan['rows']),
                               allocated_bytes=plan['allocated_bytes']))
    paths = {Path(__file__).resolve(), HERE / 'full110-settled-cache-recovery-derivation-v1.json'}
    for folder in (WRAPPER, PLANS):
        paths.update(p for p in folder.rglob('*') if p.is_file())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    destination = HERE / 'full110-recovery-plans-record-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').open('x', encoding='utf-8').write('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for number, path in enumerate(sorted(paths)):
        copy = destination / (f'{number:03d}-' + path.name)
        copy.open('xb').write(path.read_bytes())
        assert digest(copy) == digest(path)
        rows.append(dict(original=str(path), copy=copy.name, bytes=path.stat().st_size, sha256=digest(path)))
    result = dict(files=rows, original_handle=14352, original_exit=0, scopes=operations,
        original_commands=len(commands), all_seven_plans_verified=True, execution_included=False,
        compiler_invoked=False, mathematical_acceptance=False)
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), originals=len(rows), scopes=operations)), flush=True)


if __name__ == '__main__':
    main()
