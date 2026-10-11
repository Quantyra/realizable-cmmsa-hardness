"""Preserve the original once-only trace terminal and exact two-copy custody."""
import json
from pathlib import Path
import shutil
import tarfile
from custody_checks import digest, verify_local_custody
from full109_consumption_v3_controller import ROOT

HERE = Path(__file__).resolve().parent
WRAPPER = ROOT.parent / 'research-resume-20261010/20261011T021805694870Z-b1df826b68cc'
PROGRESS = ROOT.parent / 'research-resume-20261010/20261011T021722454582Z-0a1273ad6c49'
INSPECTION = ROOT.parent / 'trace-recovery-progress-v2/20261011T021732257717Z'


def read(path):
    return json.loads(Path(path).read_bytes())


def main():
    command = read(WRAPPER / 'command.json')
    assert 'native_exit' in command
    for folder in (WRAPPER, PROGRESS):
        row = read(folder / 'command.json')
        assert 'native_exit' in row
        for stream in ('stdout', 'stderr'):
            assert digest(folder / stream) == row[stream + '_sha256']
    marker = read(ROOT / 'launch-once.json')
    check = Path(marker['preflight']).resolve(strict=True)
    assert check.is_relative_to((ROOT / 'checks').resolve())
    receipt = read(check / 'terminal-custody.json')
    assert receipt['native_terminal'] and receipt['run'] == marker['run']
    custody = receipt['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    with tarfile.open(custody['repository_path']) as archive:
        terminal = json.loads(archive.extractfile('terminal.json').read())
        assert terminal == receipt['probe_terminal']
        assert int(archive.extractfile('probe.native-exit').read()) == terminal['probe_native_exit']
    paths = {ROOT / 'launch-once.json', ROOT / 'green-binding.json', Path(__file__).resolve()}
    for folder in (WRAPPER, PROGRESS, INSPECTION, check):
        paths.update(p for p in folder.rglob('*') if p.is_file())
    for folder in (ROOT.parent / 'live-trace-inspections-v1').iterdir():
        assert (folder / 'inspection.json').is_file()
        assert all(row['native_exit'] == 0 for row in read(folder / 'commands.json'))
        paths.update(p for p in folder.rglob('*') if p.is_file())
    paths.update(HERE / name for name in ('derive_full109_live_trace_inspector_v1.py',
        'inspect_full109_live_trace_v1.py', 'full109-live-trace-inspector-derivation-v1.json'))
    assert shutil.disk_usage(ROOT).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    target = HERE / 'full109-resume-trace-terminal-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    files = []
    for number, source in enumerate(sorted(paths)):
        data = source.read_bytes()
        destination = target / (f'{number:03d}-' + source.name)
        destination.open('xb').write(data)
        assert digest(source) == digest(destination)
        files.append(dict(original=str(source), copy=destination.name, bytes=len(data), sha256=digest(source)))
    value = dict(schema='full109-original-trace-terminal-custody-v1', files=files,
        original_tool_handle=34364, original_controller_native_exit=command['native_exit'],
        receipt=receipt, complete_trace_archive_preserved=True,
        trace_replayed=False, vm_stop_performed=False, qualified=False, accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), complete_original_files=len(files),
        original_controller_native_exit=command['native_exit'], probe_native_exit=terminal['probe_native_exit'],
        archive_sha256=custody['remote_sha256'], archive_bytes=custody['bytes'], accepted=False)))


if __name__ == '__main__':
    main()
