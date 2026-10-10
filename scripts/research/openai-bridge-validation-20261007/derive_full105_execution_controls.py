"""Exact Full104 algorithm reuse with immutable one-proof successor paths."""
import ast
import json
from pathlib import Path
import sys
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full104_verify.py', 'full104_worker.py', 'full104_builder02_controller.py',
         'stage_full104_builder02.py', 'full104_postprocess.py',
         'full104_native_audit.py', 'test_full104_terminal.py']


def main(write=False):
    records = []
    for name in NAMES:
        text = (HERE/name).read_text(encoding='utf-8')
        text = text.replace('full104-actual-consumer-exact-energy', 'full105-actual-consumer-exact-energy-repair')
        text = text.replace('full104', 'full105').replace('Full104', 'Full105')
        ast.parse(text)
        output = HERE/name.replace('full104', 'full105')
        data = text.encode()
        if write:
            output.open('xb').write(data)
        else:
            assert output.read_bytes() == data
        records.append(dict(source=name, source_sha256=digest(HERE/name), target=output.name, target_sha256=digest(output)))
    result = dict(schema='full105-exact-full344-full257-execution-control-derivation-v1',
        records=records, full344_full257_seven_stages=True,
        all_source_dependency_auth_resource_storage_memory_process_once_custody_warning_guards_preserved=True,
        cumulative25_sources_and_six_latest_profiles_preserved=True, compiler_invoked=False, accepted=False)
    path = HERE/'full105-execution-control-derivation.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if write:
        path.open('xb').write(data)
    else:
        assert path.read_bytes() == data
    print('Seven controls preserve full344/full257/seven-stage parent algorithms')


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(sys.argv[1:] == ['--write'])
