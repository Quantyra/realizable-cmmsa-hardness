"""Freeze full184/focused16 controls; qualification is required before use."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
PINS = {
    'full95_consumption_controller.py': '91213569E2FEC7335577E541BABE113FB358A7E625B6110A62F011F450D30DDF',
    'full95_consumption_worker.py': '3E57A9724CB476DB24840DFE7535A5D81344D2AD1271E90022B74F3BF58459C9',
    'stage_full95_consumption.py': 'CB4A0B57C61C2E903A7CA866C5C1632286BAE5AD697C002DB43C1F5EFB7CDE6A',
    'terminate_full95_consumption.py': 'BD2D632B60CDD0FA285E512508467AEBBF4699EE49207246C01864E0277800CE',
    'qualify_full95_consumption.py': 'AEB05BFF4EC2C24085A2CA702521242F7A73E161FD779418EFED63C9A59D86A1',
    'test_full95_consumption_gates.py': '569E4FC95C0812800FCA0AA7E0C9747CC6BFDD0C312FAB6D4B5BE30DE2BD7810',
}
RUN = 'cmmsa_a8_output_20261009T050952Z_3a6b1f17'


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise RuntimeError('Unexpected parent control structure: ' + before)
    return text.replace(before, after, 1)


def transformed(name):
    if digest(HERE / name) != PINS[name]:
        raise RuntimeError('Full95 parent control drift: ' + name)
    text = (HERE / name).read_text(encoding='utf-8')
    text = text.replace('full95', 'full97').replace('Full95', 'Full97')
    text = text.replace('cmmsa_a8_output_20261009T023928Z_13a1218e', RUN)
    text = text.replace('13a1218e', '3a6b1f17')
    text = text.replace('full97-manuscript-moment-syntax-repair',
                        'full97-spectral-bridge-utf8-section-repair')
    text = text.replace('323', '325').replace('653', '657').replace('181', '184')
    text = text.replace('(184,13)', '(184,16)')
    text = text.replace('focused-thirteen-consumer', 'focused-sixteen-consumer')
    text = text.replace("!= 13:", "!= 16:")
    if name == 'full95_consumption_controller.py':
        text = replace_once(text,
            'REQUESTS = SOURCE_SIZE_REQUESTS + DYADIC_REQUESTS',
            'from prepare_builder02_full97 import REQUESTS as BRIDGE_REQUESTS\n'
            'REQUESTS = SOURCE_SIZE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS')
        text = replace_once(text,
            "    require_qualified_green(audited, qualified, custody['remote_sha256'])\n",
            "    require_qualified_green(audited, qualified, custody['remote_sha256'])\n"
            "    with tarfile.open(custody['repository_path']) as archive:\n"
            "        native_objects = json.loads(archive.extractfile('object-after.json').read())\n"
            "    if len(native_objects) != 657:\n"
            "        raise RuntimeError('Complete Full97 native object inventory required')\n")
    if name == 'full95_consumption_worker.py':
        text = replace_once(text,
            "    if len(project_objects) != 325 or not project_objects <= set(objects):\n",
            "    if len(project_objects) != 325 or len(objects) != 657 or not project_objects <= set(objects):\n")
    ast.parse(text, filename=name.replace('full95', 'full97'))
    return text.encode('utf-8')


def main(verify=False):
    rows = []
    for name in PINS:
        data = transformed(name)
        target = HERE / name.replace('full95', 'full97')
        if verify:
            if target.read_bytes() != data:
                raise RuntimeError('Full97 controls differ from their frozen derivation')
        else:
            with target.open('xb') as output:
                output.write(data)
        rows.append(dict(parent=name, parent_sha256=PINS[name],
                         output=target.name, output_sha256=digest(target)))
    record = HERE / 'full97-consumption-control-derivation.json'
    value = dict(schema='full97-full184-focused16-controls-v1', controls=rows,
        run=RUN, sources=325, roots=184, focused=16, expected_native_objects=657,
        native_object_count_requires_actual_terminal_verification=True,
        native_qualified_green_and_termination_required=True,
        original_guards_preserved=True, added_guard='exact657-native-object-inventory',
        compiler_invoked=False, cloud_operation=False, accepted=False)
    if verify:
        if json.loads(record.read_bytes()) != value:
            raise RuntimeError('Full97 derivation receipt drift')
    else:
        with record.open('x', encoding='utf-8', newline='\n') as output:
            json.dump(value, output, indent=2)
            output.write('\n')
    print('Full97 full184/focused16 controls ' + ('verified' if verify else 'frozen')
          + '; no compiler or cloud operation')


if __name__ == '__main__':
    if sys.argv[1:] not in ([], ['--verify']):
        raise SystemExit('Use initial derivation or --verify')
    main(sys.argv[1:] == ['--verify'])
