"""Preserve the sole first-SSH staging failure before the guarded continuation."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full110_builder02_controller import ROOT, VM

HERE = Path(__file__).resolve().parent


def main():
    wrapper = ROOT / 'research-resume-20261011/20261011T024521895176Z-f745a84589ca'
    stage = ROOT / 'staging-controls/20261011T024642675770Z'
    terminal = json.loads((wrapper / 'command.json').read_bytes())
    assert terminal['native_exit'] == 1
    for stream in ('stdout', 'stderr'):
        assert digest(wrapper / stream) == terminal[stream + '_sha256']
    commands = json.loads((stage / 'commands.json').read_bytes())
    assert len(commands) == 5 and [r['native_exit'] for r in commands] == [0, 0, 0, 0, 1]
    assert commands[-1]['argv'][1:4] == ['compute', 'ssh', VM]
    assert commands[2]['argv'][1:5] == ['compute', 'instances', 'start', VM]
    for number, command in enumerate(commands):
        for stream in ('stdout', 'stderr'):
            assert digest(stage / f'{number}.{stream}') == command[stream + '_sha256']
    assert not (ROOT / 'launch-once.json').exists()
    paths = {p for folder in (wrapper, stage) for p in folder.iterdir() if p.is_file()}
    paths.add(Path(__file__).resolve())
    target = HERE / 'full110-resume-staging-failure-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = target / (f'{number:03d}-'+original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    result = dict(schema='full110-original-staging-first-SSH-failure-v1', files=rows,
        original_tool_handle=36405, original_native_exit=1, exact_vm_start_native_exit=0,
        first_SSH_native_exit=1, SSH_error='Remote side unexpectedly closed network connection; plink exit1',
        compiler_invoked=False, launch_marker_absent=True, remote_stage_absence_not_yet_verified=True,
        guarded_resume_requires_exact_running_identity_and_remote_stage_absence=True,
        original_failed_attempt_preserved=True, accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), original_files=len(rows), original_native_exit=1, compiler_invoked=False)))


if __name__ == '__main__':
    main()
