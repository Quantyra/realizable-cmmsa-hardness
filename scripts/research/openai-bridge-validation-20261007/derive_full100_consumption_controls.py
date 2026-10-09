"""Derive complete Full100 trace controls; native qualification is mandatory."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full99_consumption_controller.py','full99_consumption_worker.py',
         'stage_full99_consumption.py','terminate_full99_consumption.py',
         'qualify_full99_consumption.py','test_full99_consumption_gates.py']

def expected(name):
    text = (HERE/name).read_text(encoding='utf-8')
    text = text.replace('full99','full100').replace('Full99','Full100')
    ast.parse(text)
    return text.encode('utf-8')

def main(write=False):
    rows = []
    for name in NAMES:
        data = expected(name)
        target = HERE/name.replace('full99','full100')
        if write:
            with target.open('xb') as stream: stream.write(data)
        else: assert target.read_bytes() == data
        rows.append(dict(parent=name,parent_sha256=digest(HERE/name),output=target.name,output_sha256=digest(target)))
    value = dict(schema='full100-full192-focused24-control-derivation-v1',controls=rows,
        sources=327,roots=192,focused=24,expected_native_objects=661,
        native_object_count_requires_actual_terminal_verification=True,
        native_qualification_custody_and_independent_termination_required=True,
        compile_or_probe_executed=False,launch_clearance=False,accepted=False)
    receipt = HERE/'full100-consumption-control-derivation.json'
    if write:
        with receipt.open('xb') as stream: stream.write((json.dumps(value,indent=2)+'\n').encode())
    else: assert json.loads(receipt.read_bytes()) == value
    print('Six complete Full100 trace controls reproduce parent with explicit scope/name bindings; no probe launch')

if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
