"""Preserve settled recovery boot and idle refresh without snapshotting live planning."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full110_builder02_controller import ROOT, VM, VM_ID

HERE = Path(__file__).resolve().parent
RECOVERY = ROOT / 'settled-cache-recovery-v1'


def main():
    boot = json.loads((RECOVERY / 'boot-result.json').read_bytes())
    assert boot['before']['status'] == 'TERMINATED' and boot['after']['status'] == 'RUNNING'
    assert boot['before']['name'] == boot['after']['name'] == VM
    assert str(boot['before']['id']) == str(boot['after']['id']) == VM_ID
    assert not boot['compiler_invoked']
    idle, = (RECOVERY / 'idle-refresh-controls').glob('*/idle-refreshed.json')
    refresh = json.loads(idle.read_bytes())
    assert refresh['idle_timer_active'] and refresh['idle_activity_refreshed']
    assert not refresh['compiler_invoked'] and not refresh['power_operation']
    paths = {RECOVERY / 'boot-once.json', RECOVERY / 'boot-result.json', Path(__file__).resolve()}
    for folder in (Path(boot['control']), idle.parent):
        for row in json.loads((folder / 'commands.json').read_bytes()):
            assert row['native_exit'] == 0 and not row['timed_out']
            for stream in ('stdout', 'stderr'):
                assert digest(folder / row[stream + '_path']) == row[stream + '_sha256']
        paths.update(p for p in folder.rglob('*') if p.is_file())
    wrappers = [('20261011T030653515927Z-77589d84eb42', 92676),
                ('20261011T031726525617Z-fe123d76bbd0', 54018)]
    for name, handle in wrappers:
        folder = ROOT / 'research-resume-20261011' / name
        command = json.loads((folder / 'command.json').read_bytes())
        assert command['native_exit'] == 0
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == command[stream + '_sha256']
        paths.update(p for p in folder.iterdir() if p.is_file())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    destination = HERE / 'full110-recovery-lifecycle-start-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').open('x', encoding='utf-8').write('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows = []
    for number, path in enumerate(sorted(paths)):
        copy = destination / (f'{number:03d}-' + path.name)
        copy.open('xb').write(path.read_bytes())
        assert digest(copy) == digest(path)
        rows.append(dict(original=str(path), copy=copy.name, bytes=path.stat().st_size, sha256=digest(path)))
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(dict(
        files=rows, original_handles=dict(boot=92676, idle_refresh=54018), original_exits=[0, 0],
        historical_recovery_start=boot, historical_idle_refresh=refresh,
        live_plan_14352_excluded=True, cache_execution_or_compiler_acceptance=False), indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), originals=len(rows), all_bytes_verified=True)), flush=True)


if __name__ == '__main__':
    main()
