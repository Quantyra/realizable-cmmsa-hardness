"""Exact Full102 algorithm reuse, with immutable successor bindings."""
import ast
import json
import sys
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full102_verify.py','full102_worker.py','full102_builder02_controller.py',
         'stage_full102_builder02.py','full102_postprocess.py','full102_native_audit.py','test_full102_terminal.py']


def main(write=False):
    rows = []
    for name in NAMES:
        text = (HERE/name).read_text(encoding='utf-8').replace('full102', 'full103')
        ast.parse(text)
        path = HERE/name.replace('full102', 'full103')
        data = text.encode()
        if write: path.open('xb').write(data)
        else: assert path.read_bytes() == data
        rows.append(dict(source=name,source_sha256=digest(HERE/name),target=path.name,target_sha256=digest(path)))
    record = HERE/'full103-execution-control-derivation.json'
    data = (json.dumps(dict(schema='full103-exact-control-derivation-v1',records=rows,
        full340_full251_seven_stages=True,all_execution_and_warning_custody_guards_preserved=True,
        compiler_invoked=False),indent=2)+'\n').encode()
    if write: record.open('xb').write(data)
    else: assert record.read_bytes() == data
    print('Seven controls preserve exact parent algorithms and resource guards')


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(sys.argv[1:] == ['--write'])
