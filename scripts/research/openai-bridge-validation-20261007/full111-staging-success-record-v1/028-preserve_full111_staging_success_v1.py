"""Capture original Full111 transport/preflight on the audited recovery lifecycle."""
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full111_builder02_controller import ROOT, VM_ID
from audit_full110_settled_cache_recovery_v2 import AUDIT, validate_local_audit

HERE = Path(__file__).resolve().parent


def main():
    validate_local_audit()
    wrappers = []
    for path in (ROOT / 'research-resume-20261011').glob('*/command.json'):
        row = json.loads(path.read_bytes())
        if row['argv'][-1].endswith('stage_full111_after_recovery_v2.py'):
            wrappers.append(path.parent)
    assert len(wrappers) == 1
    wrapper = wrappers[0]
    command = json.loads((wrapper / 'command.json').read_bytes())
    assert command['native_exit'] == 0
    for stream in ('stdout', 'stderr'):
        assert digest(wrapper / stream) == command[stream + '_sha256']
    stages = list((ROOT / 'staging-controls').glob('*/staged.json'))
    assert len(stages) == 1
    stage = stages[0].parent
    commands = json.loads((stage / 'commands.json').read_bytes())
    assert len(commands) == 10 and all(row['native_exit'] == 0 for row in commands)
    assert not any(row['argv'][1:4] == ['compute', 'instances', 'start'] for row in commands)
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
    admission = json.loads((stage / 'recovery-admission.json').read_bytes())
    assert admission['sha256'] == digest(AUDIT / 'audit.json')
    assert admission['all_seven_recovery_scopes_verified'] and not admission['VM_start_performed']
    paths = {p for folder in (wrapper, stage) for p in folder.iterdir() if p.is_file()}
    paths.add(Path(__file__).resolve())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    target = HERE / 'full111-staging-success-record-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = target / (f'{number:03d}-' + original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    result = dict(schema='full111-original-staging-success-v1', files=rows, original_native_exit=0,
        original_wrapper=str(wrapper), original_stage=str(stage), staged=staged, recovery_admission=admission,
        existing_recovery_lifecycle=True, second_VM_start_performed=False,
        staging_compiler_invoked=False, native_acceptance=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), original_files=len(rows), original_native_exit=0,
        source_count=369, warm_objects=566, staging_compiler_invoked=False)), flush=True)


if __name__ == '__main__':
    main()
