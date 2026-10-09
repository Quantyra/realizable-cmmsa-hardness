"""Derive full181/focused13 controls from frozen Full92 templates; no execution."""
import ast
import json
from pathlib import Path
from custody_checks import digest
HERE = Path(__file__).parent

def main():
    names = ['full92_consumption_controller.py', 'full92_consumption_worker.py',
             'stage_full92_consumption.py', 'terminate_full92_consumption.py',
             'qualify_full92_consumption.py', 'test_full92_consumption_gates.py']
    rows = []
    for name in names:
        text = (HERE/name).read_text(encoding='utf-8')
        text = text.replace('full92', 'full95').replace('Full92', 'Full95')
        text = text.replace('cmmsa_a8_output_20261008T222156Z_b32c7fb4', 'cmmsa_a8_output_20261009T023928Z_13a1218e')
        text = text.replace('b32c7fb4', '13a1218e')
        text = text.replace('full95-source-size-profile-resource02', 'full95-manuscript-moment-syntax-repair-resource02')
        text = text.replace('full95-source-size-profile-builder02-stage', 'full95-manuscript-moment-syntax-repair-builder02-stage')
        text = text.replace('322', '323').replace('651', '653').replace('178', '181')
        text = text.replace('(181,10)', '(181,13)').replace('focused-ten-consumer', 'focused-thirteen-consumer')
        text = text.replace("!= 10:", "!= 13:")
        if name == 'full92_consumption_controller.py':
            text = text.replace('from prepare_builder02_full95 import OUTPUT, REQUESTS',
                'from prepare_builder02_full95 import OUTPUT\nfrom prepare_builder02_full91 import REQUESTS as SOURCE_SIZE_REQUESTS\nfrom prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS\nREQUESTS = SOURCE_SIZE_REQUESTS + DYADIC_REQUESTS')
        output = HERE/name.replace('full92','full95')
        ast.parse(text, filename=str(output))
        with output.open('x',encoding='utf-8',newline='\n') as stream: stream.write(text)
        rows.append(dict(parent=name,parent_sha256=digest(HERE/name),output=output.name,output_sha256=digest(output)))
    with (HERE/'full95-consumption-control-derivation.json').open('x',encoding='utf-8') as stream:
        json.dump(dict(schema='full95-full181-focused13-controls-v1',controls=rows,
            run='cmmsa_a8_output_20261009T023928Z_13a1218e',sources=323,roots=181,focused=13,
            expected_native_objects=653,native_qualified_green_and_termination_required=True,
            original_guards_preserved=True,compiler_invoked=False,accepted=False),stream,indent=2)
        stream.write('\n')
    print('Derived Full95 controls; no compiler or cloud operation')

if __name__ == '__main__': main()
