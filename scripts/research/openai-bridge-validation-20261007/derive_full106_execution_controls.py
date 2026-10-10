"""Derive parent controls with explicit additive scope and new immutable paths."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full105_verify.py', 'full105_worker.py', 'full105_builder02_controller.py',
         'stage_full105_builder02.py', 'full105_postprocess.py',
         'full105_native_audit.py', 'test_full105_terminal.py']


def transformed(name):
    text = (HERE/name).read_text(encoding='utf-8')
    text = text.replace('full105-actual-consumer-exact-energy-repair', 'full106-exact-product-energy')
    text = text.replace('full105', 'full106').replace('Full105', 'Full106')
    text = text.replace('344', '346').replace('257', '260')
    if name == 'full105_verify.py':
        assert "manifest['requested_axioms'][-6:]" in text
        text = text.replace("manifest['requested_axioms'][-6:]", "manifest['requested_axioms'][-3:]")
    if name == 'full105_native_audit.py':
        assert "len(additive['added_sources']) != 25" in text
        text = text.replace("len(additive['added_sources']) != 25", "len(additive['added_sources']) != 27")
        text += '\n'  # Separate derived native record; capture-time false flags remain historical.
    if name == 'full105_builder02_controller.py':
        old = "'derive_full106_execution_controls.py',"
        assert old in text
        text = text.replace(old, old+"'prepare_full106_product_energy_scope.py','test_full106_scope.py',")
    ast.parse(text)
    return text.encode()


def main(write=False):
    rows = []
    for name in NAMES:
        output = HERE/name.replace('full105', 'full106')
        data = transformed(name)
        if write:
            output.open('xb').write(data)
        else:
            assert output.read_bytes() == data
        rows.append(dict(source=name, source_sha256=digest(HERE/name),
                         target=output.name, target_sha256=digest(output)))
    record = dict(schema='full106-parent-algorithm-additive-scope-control-derivation-v1', records=rows,
                  scope=dict(parent_sources=344, sources=346, parent_profiles=257, profiles=260,
                             cumulative_added_sources=27, latest_added_profiles=3, stages=7),
                  source_dependency_auth_resource_storage_memory_process_once_custody_warning_guards_preserved=True,
                  compiler_invoked=False, launch_clearance=False, accepted=False)
    path = HERE/'full106-execution-control-derivation.json'
    data = (json.dumps(record, indent=2)+'\n').encode()
    if write:
        path.open('xb').write(data)
    else:
        assert path.read_bytes() == data
    print('Seven controls derived; full346/full260; unchanged gates and additive scope only')


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(sys.argv[1:] == ['--write'])
