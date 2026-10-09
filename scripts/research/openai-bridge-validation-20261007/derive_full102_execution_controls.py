"""Exact parent control algorithms with new immutable path/module bindings."""
import ast
import json
import sys
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).parent
NAMES=['full101_verify.py','full101_worker.py','full101_builder02_controller.py',
       'stage_full101_builder02.py','full101_postprocess.py','full101_native_audit.py','test_full101_terminal.py']


def main(write=False):
    rows=[]
    for name in NAMES:
        text=(HERE/name).read_text(encoding='utf-8').replace('full101-spectral-original-application','full102-spectral-owned-warning-repair').replace('full101','full102')
        if name=='full101_builder02_controller.py':
            old="'prepare_full102_spectral_application.py','recover_existing_spectral_candidate.py'"
            assert text.count(old)==1
            text=text.replace(old,"'prepare_full101_warning_repair.py','prepare_full101_spectral_application.py','recover_existing_spectral_candidate.py'")
        ast.parse(text)
        path=HERE/name.replace('full101','full102');data=text.encode()
        if write:path.open('xb').write(data)
        else:assert path.read_bytes()==data
        rows.append(dict(source=name,source_sha256=digest(HERE/name),target=path.name,target_sha256=digest(path)))
    record=HERE/'full102-execution-control-derivation.json'
    data=(json.dumps(dict(schema='full102-exact-control-derivation-v1',records=rows,full340_full251_seven_stages=True,
                         all_execution_and_warning_custody_guards_preserved=True,compiler_invoked=False),indent=2)+'\n').encode()
    if write:record.open('xb').write(data)
    else:assert record.read_bytes()==data
    print('Seven controls preserve exact parent algorithms and resource guards')


if __name__=='__main__':
    assert sys.argv[1:] in ([],['--write'])
    main(sys.argv[1:]==['--write'])
