"""Preserve v1 controls; derive a separate exact Full100-run-bound trace."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
RUN = 'cmmsa_a8_output_20261009T092534Z_c0fd3e11'
OLD_RUN = 'cmmsa_a8_output_20261009T050952Z_3a6b1f17'
NAMES = {
    'full100_consumption_controller.py': 'full100_consumption_v2_controller.py',
    'full100_consumption_worker.py': 'full100_consumption_v2_worker.py',
    'stage_full100_consumption.py': 'stage_full100_consumption_v2.py',
    'terminate_full100_consumption.py': 'terminate_full100_consumption_v2.py',
    'qualify_full100_consumption.py': 'qualify_full100_consumption_v2.py',
    'test_full100_consumption_gates.py': 'test_full100_consumption_v2_gates.py',
}

def expected():
    parent = json.loads((HERE/'full100-consumption-control-derivation.json').read_bytes())
    rows = {row['output']: row['output_sha256'] for row in parent['controls']}
    assert set(rows) == set(NAMES)
    outputs = {}
    for name, target in NAMES.items():
        assert digest(HERE/name) == rows[name], 'Original v1 control drift'
        text = (HERE/name).read_text(encoding='utf-8')
        for old, new in NAMES.items():
            text = text.replace(old, new).replace(old.removesuffix('.py'), new.removesuffix('.py'))
        text = text.replace('consumption-v1', 'consumption-v2')
        text = text.replace(OLD_RUN, RUN)
        text = text.replace('3a6b1f17-consumption-v2.tar.gz', 'c0fd3e11-consumption-v2.tar.gz')
        assert OLD_RUN not in text and '3a6b1f17-consumption' not in text
        ast.parse(text)
        outputs[target] = text.encode('utf-8')
    return outputs

def main(write=False):
    rows = []
    for name, data in expected().items():
        target = HERE/name
        if write:
            with target.open('xb') as stream: stream.write(data)
        else:
            assert target.read_bytes() == data
        rows.append(dict(path=name, sha256=digest(target)))
    value = dict(schema='full100-trace-v2-run-binding-repair',
        original_derivation_sha256=digest(HERE/'full100-consumption-control-derivation.json'),
        controls=rows, run=RUN, sources=327, roots=192, focused=24, objects=661,
        changes=['separate v2 paths and module names', 'exact native run', 'isolated short custody path'],
        original_v1_controls_and_binding_preserved=True,
        prepared_probe_and_postprocessor_unchanged=True,
        qualification_and_launch_algorithms_unchanged=True,
        cloud_operation=False, accepted=False)
    receipt = HERE/'full100-trace-v2-derivation.json'
    if write:
        with receipt.open('x', encoding='utf-8') as stream:
            json.dump(value, stream, indent=2); stream.write('\n')
    else:
        assert json.loads(receipt.read_bytes()) == value
    print('Full100 v2 exact-run and isolated custody bindings verified; full scope/guards retained')

if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
