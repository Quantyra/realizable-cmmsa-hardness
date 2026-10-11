"""Preserve settled read-only progress observations without claiming native completion."""
import ast
import base64
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full110_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
OBSERVATIONS = {'20261011T025433031247Z': 90558, '20261011T025814062775Z': 42415}
CONTROLS = ('derive_full110_native_inspector_v1.py', 'derive_full110_native_inspector_v2.py',
            'inspect_full110_native_progress_v1.py', 'inspect_full110_native_progress_v2.py',
            'full110-native-inspector-derivation-v1.json', 'full110-native-inspector-derivation-v2.json')


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    assert marker['run'] == 'cmmsa_a8_output_20261011T025221Z_7046a7c0'
    paths = {ROOT / 'launch-once.json', Path(marker['preflight']) / 'preflight.json', Path(__file__).resolve()}
    paths.update(HERE / name for name in CONTROLS)
    source = HERE / 'inspect_full110_native_progress_v1.py'
    derivation = json.loads((HERE / 'full110-native-inspector-derivation-v2.json').read_bytes())
    assert digest(source) == derivation['source_sha256']
    text = source.read_text(encoding='utf-8')
    for old, new in derivation['exact_replacements']:
        assert text.count(old) == 1
        text = text.replace(old, new)
    target = HERE / 'inspect_full110_native_progress_v2.py'
    assert target.read_bytes() == text.encode('utf-8')
    assert digest(target) == derivation['target_sha256']
    for name in CONTROLS:
        if name.endswith('.py'):
            ast.parse((HERE / name).read_text(encoding='utf-8'))
    observations = []
    for name, handle in OBSERVATIONS.items():
        folder = ROOT / 'live-native-inspections-v2' / name
        commands = json.loads((folder / 'commands.json').read_bytes())
        assert len(commands) == 2 and all(row['native_exit'] == 0 for row in commands)
        for number, row in enumerate(commands):
            for stream in ('stdout', 'stderr'):
                assert digest(folder / f'{number}.{stream}') == row[stream + '_sha256']
        value = json.loads((folder / 'inspection.json').read_bytes())
        assert value == json.loads((folder / '1.stdout').read_bytes())
        assert value['run'] == marker['run'] and value['read_only'] and not value['compiler_replayed']
        assert value['observed_snapshots_not_authoritative_terminal_custody']
        for stream, row in value['streams'].items():
            data = base64.b64decode(row['base64'], validate=True)
            observed = folder / 'observed-streams' / stream
            assert Path(stream).name == stream and observed.read_bytes() == data
            assert len(data) == row['bytes'] and digest(observed) == row['sha256']
        cleanup = json.loads((folder / 'owned-tunnel-cleanup.json').read_bytes())
        assert cleanup['native_exit'] == 0 and cleanup['only_owned_tunnel_targeted']
        observations.append(dict(folder=str(folder), original_handle=handle, native_exit=0,
            stage_exits=[row['native_exit'] for row in value['stages']],
            disk_available_bytes=value['disk_available_bytes'],
            full_observed_streams=len(value['streams']), authoritative_terminal_custody=False))
        paths.update(p for p in folder.rglob('*') if p.is_file())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    destination = HERE / 'full110-resume-native-progress-v1'
    destination.mkdir(exist_ok=False)
    (destination / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = destination / (f'{number:03d}-' + original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    index = dict(schema='full110-live-native-progress-custody-v1', files=rows, observations=observations,
        original_controller_handle=56715, original_controller_pid=5236, run=marker['run'],
        controller_live_at_observation=True, native_completion_claimed=False, accepted=False, full_goal_complete=False,
        unused_v1_stage_index_draft_preserved=True, original_compiler_restarted=False)
    (destination / 'index.json').open('x', encoding='utf-8').write(json.dumps(index, indent=2)+'\n')
    print(json.dumps(dict(folder=str(destination), original_files=len(rows), observations=observations)))


if __name__ == '__main__':
    main()
