"""Preserve two original read-only Full111 snapshots without terminal claims."""
import base64
import json
from pathlib import Path
import shutil
from custody_checks import digest
from full111_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent
OBSERVATIONS = [('20261011T035925806193Z', 40829), ('20261011T040238010816Z', 19889)]


def main():
    marker = json.loads((ROOT / 'launch-once.json').read_bytes())
    assert marker['run'] == 'cmmsa_a8_output_20261011T035621Z_498f7ba6'
    derivation = json.loads((HERE / 'full111-native-inspector-derivation-v1.json').read_bytes())
    assert digest(Path(derivation['source'])) == derivation['source_sha256']
    after = Path(derivation['source']).read_text(encoding='utf-8')
    for row in derivation['exact_replacements']:
        assert after.count(row['before']) == row['count']
        after = after.replace(row['before'], row['after'])
    assert Path(derivation['target']).read_bytes() == after.encode('utf-8')
    assert digest(Path(derivation['target'])) == derivation['target_sha256']
    paths = {ROOT / 'launch-once.json', Path(marker['preflight']) / 'preflight.json', Path(__file__).resolve(),
             HERE / 'derive_full111_native_inspector_v1.py', HERE / 'full111-native-inspector-derivation-v1.json',
             Path(derivation['target'])}
    observations = []
    for name, handle in OBSERVATIONS:
        folder = ROOT / 'live-native-inspections-v1' / name
        commands = json.loads((folder / 'commands.json').read_bytes())
        assert len(commands) == 2 and all(row['native_exit'] == 0 for row in commands)
        for number, row in enumerate(commands):
            for stream in ('stdout', 'stderr'):
                assert digest(folder / f'{number}.{stream}') == row[stream + '_sha256']
        value = json.loads((folder / 'inspection.json').read_bytes())
        assert value == json.loads((folder / '1.stdout').read_bytes())
        assert value['run'] == marker['run'] and value['read_only'] and not value['compiler_replayed']
        assert value['observed_snapshots_not_authoritative_terminal_custody']
        for name, row in value['streams'].items():
            path = folder / 'observed-streams' / name
            assert Path(name).name == name
            assert path.read_bytes() == base64.b64decode(row['base64'], validate=True)
            assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
        cleanup = json.loads((folder / 'owned-tunnel-cleanup.json').read_bytes())
        assert cleanup['native_exit'] == 0 and cleanup['only_owned_tunnel_targeted']
        observations.append(dict(folder=str(folder), original_handle=handle, native_exit=0,
            stage_exits=[r['native_exit'] for r in value['stages']],
            complete_observed_streams=len(value['streams']), native_completion_claimed=False))
        paths.update(p for p in folder.rglob('*') if p.is_file())
    assert shutil.disk_usage(HERE).free - sum(p.stat().st_size for p in paths) >= 1536 * 1024**2
    target = HERE / 'full111-native-progress-record-v1'
    target.mkdir(exist_ok=False)
    (target / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    rows = []
    for number, original in enumerate(sorted(paths)):
        copy = target / (f'{number:03d}-' + original.name)
        with original.open('rb') as source, copy.open('xb') as output:
            shutil.copyfileobj(source, output)
        assert digest(copy) == digest(original)
        rows.append(dict(original=str(original), copy=copy.name, bytes=original.stat().st_size, sha256=digest(original)))
    value = dict(schema='full111-native-progress-v1', files=rows, observations=observations,
        original_controller_handle=60064, original_controller_pid=6012, run=marker['run'],
        original_compiler_replayed=False, native_completion_claimed=False, accepted=False, full_goal_complete=False)
    (target / 'index.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(dict(folder=str(target), complete_originals=len(rows), observations=observations)), flush=True)


if __name__ == '__main__':
    main()
