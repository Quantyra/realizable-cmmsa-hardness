"""Preserve the original guarded staging continuation and complete GCP preflight."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full110_builder02_controller import ROOT, VM_ID

HERE = Path(__file__).resolve().parent


def main():
    wrapper = ROOT / 'research-resume-20261011/20261011T024848653260Z-ba14a489e82d'
    stage = ROOT / 'staging-controls/20261011T024931402882Z'
    command = json.loads((wrapper / 'command.json').read_bytes())
    assert command['native_exit'] == 0 and command['argv'][-1] == '--resume-staging'
    for stream in ('stdout', 'stderr'):
        assert digest(wrapper / stream) == command[stream + '_sha256']
    commands = json.loads((stage / 'commands.json').read_bytes())
    assert len(commands) == 10 and all(r['native_exit'] == 0 for r in commands)
    assert not any(r['argv'][1:4] == ['compute', 'instances', 'start'] for r in commands)
    for number, row in enumerate(commands):
        for stream in ('stdout', 'stderr'):
            assert digest(stage / f'{number}.{stream}') == row[stream + '_sha256']
    staged = json.loads((stage / 'staged.json').read_bytes())
    preflight = staged['dependency_preflight']
    assert str(staged['after']['id']) == VM_ID and staged['after']['status'] == 'RUNNING'
    assert (preflight['project_sources_verified'], preflight['warm_objects_verified']) == (369, 566)
    assert (preflight['package_sources_verified'], preflight['core_sources_verified']) == (11574, 2520)
    assert preflight['external_ip_absent'] and preflight['idle_timer_active']
    assert not preflight['active_compiler_pids'] and not staged['compiler_invoked']
    assert preflight['disk_available_bytes'] >= 40 * 1024**3
    assert preflight['available_memory_bytes'] >= 48 * 1024**3
    paths = {p for folder in (wrapper, stage) for p in folder.iterdir() if p.is_file()}
    paths.add(Path(__file__).resolve())
    target = HERE / 'full110-resume-staging-success-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = target / (f'{number:03d}-'+original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    result = dict(schema='full110-original-guarded-staging-success-v1', files=rows,
        original_tool_handle=64527, original_native_exit=0, staged=staged,
        original_failed_staging_preserved=True, second_VM_start_performed=False,
        remote_stage_absence_verified_before_continuation=True,
        staging_compiler_invoked=False, staging_launch_clearance=False,
        next_original_native_controller_handle=56715, native_acceptance=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), original_files=len(rows), original_native_exit=0,
                         source_count=369, warm_objects=566, staging_compiler_invoked=False)))


if __name__ == '__main__':
    main()
