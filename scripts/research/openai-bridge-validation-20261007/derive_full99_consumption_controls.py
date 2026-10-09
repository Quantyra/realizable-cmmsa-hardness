"""Derive complete Full99 trace controls; native qualification is mandatory."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full97_consumption_controller.py','full97_consumption_worker.py',
         'stage_full97_consumption.py','terminate_full97_consumption.py',
         'qualify_full97_consumption.py','test_full97_consumption_gates.py']

def expected(name):
    text = (HERE/name).read_text(encoding='utf-8')
    text = text.replace('full97','full99').replace('Full97','Full99')
    text = text.replace('full99-spectral-bridge-utf8-section-repair', 'full99-matrix-fourier-bullet-repair')
    text = text.replace('325','327').replace('657','661').replace('184','192')
    text = text.replace('(192,16)', '(192,24)').replace('focused-sixteen-consumer','focused-twentyfour-consumer')
    text = text.replace("!= 16:", "!= 24:")
    ast.parse(text)
    return text.encode('utf-8')

def main(write=False):
    rows = []
    for name in NAMES:
        data = expected(name)
        target = HERE/name.replace('full97','full99')
        if write:
            with target.open('xb') as stream: stream.write(data)
        else: assert target.read_bytes() == data
        rows.append(dict(parent=name,parent_sha256=digest(HERE/name),output=target.name,output_sha256=digest(target)))
    value = dict(schema='full99-full192-focused24-control-derivation-v1',controls=rows,
        sources=327,roots=192,focused=24,expected_native_objects=661,
        native_object_count_requires_actual_terminal_verification=True,
        native_qualification_custody_and_independent_termination_required=True,
        compile_or_probe_executed=False,launch_clearance=False,accepted=False)
    receipt = HERE/'full99-consumption-control-derivation.json'
    if write:
        with receipt.open('xb') as stream: stream.write((json.dumps(value,indent=2)+'\n').encode())
    else: assert json.loads(receipt.read_bytes()) == value
    print('Six complete Full99 trace controls reproduce parent with explicit scope/name bindings; no probe launch')

if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(bool(sys.argv[1:]))
