"""Correct the unexecuted inspector's stage indices to the frozen zero-based manifest."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from full110_builder02_controller import ROOT

HERE = Path(__file__).resolve().parent


def main():
    manifest = json.loads((ROOT / 'capture-manifest.json').read_bytes())
    assert [row['index'] for row in manifest['stages']] == list(range(7))
    assert not (ROOT / 'live-native-inspections-v1').exists()
    source = HERE / 'inspect_full110_native_progress_v1.py'
    assert digest(source) == '47173A353AD24BA57C7187643521197342D67C296D963336C00011056E169499'
    replacements = [('range(1,8)', 'range(7)'), ("'live-native-inspections-v1'", "'live-native-inspections-v2'")]
    after = source.read_text(encoding='utf-8')
    for old, new in replacements:
        assert after.count(old) == 1
        after = after.replace(old, new)
    ast.parse(after)
    target = HERE / 'inspect_full110_native_progress_v2.py'
    target.open('xb').write(after.encode('utf-8'))
    value = dict(source=str(source), source_sha256=digest(source), target=str(target), target_sha256=digest(target),
                 exact_replacements=replacements, stages=list(range(7)),
                 original_v1_inspector_unexecuted_and_preserved=True,
                 no_observation_omits_stage_zero=True, read_only=True,
                 unchanged_transport_and_host_key_guards=True, compiler_invoked=False)
    (HERE / 'full110-native-inspector-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(value))


if __name__ == '__main__':
    main()
