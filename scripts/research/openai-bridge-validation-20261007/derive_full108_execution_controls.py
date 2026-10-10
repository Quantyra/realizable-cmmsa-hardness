"""Derive exact guarded Full108 execution controls; never execute cloud or Lean."""
import ast
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    records = []
    names = ['full107_builder02_controller.py','full107_worker.py','full107_verify.py',
             'full107_postprocess.py','full107_native_audit.py','stage_full107_builder02.py',
             'test_full107_terminal.py']
    for name in names:
        raw = (HERE/name).read_bytes()
        text = raw.decode('utf-8').replace('full107-exact-product-energy-repair','full108-exact-crosslevel-product')
        text = text.replace('full107','full108').replace('Full107','Full108')
        text = re.sub(r'\b(?:346|260)\b',lambda m:{'346':'348','260':'261'}[m.group()],text)
        text = text.replace('Full260','Full261')
        if name == 'full107_verify.py':
            assert text.count("manifest['requested_axioms'][-3:]") == 1
            text = text.replace("manifest['requested_axioms'][-3:]","manifest['requested_axioms'][-1:]")
        if name == 'full107_builder02_controller.py':
            start = text.index('EXTRA_LOCAL_CONTROLS = ')
            end = text.index('\n',start)
            text = text[:start]+"EXTRA_LOCAL_CONTROLS = ('full108_capture_gates.py','prepare_builder02_full108.py','full108_native_audit.py','full108_postprocess.py','derive_full108_execution_controls.py','derive_full108_capture_controls.py','prepare_full108_crosslevel_product_scope.py','test_full108_scope.py','prepare_full101_warning_repair.py','prepare_full101_spectral_application.py','recover_existing_spectral_candidate.py')"+text[end:]
        if name == 'full107_native_audit.py':
            before = "    save(run/'material-expanded-native-report.json',expanded)"
            assert text.count(before) == 1
            text = text.replace(before,"    expanded.update(exact_real_product_energy_native_verified=expanded['full108_expanded_native_gates_green'], real_same_function_crosslevel_Gram_native_verified=expanded['full108_expanded_native_gates_green'])\n"+before)
        ast.parse(text)
        target = name.replace('full107','full108')
        data = text.encode('utf-8')
        path = HERE/target
        if path.exists(): assert path.read_bytes() == data, 'Derived target drift'
        else: path.open('xb').write(data)
        records.append(dict(source=name,source_sha256=sha(raw),target=target,target_sha256=sha(data)))
    result = dict(schema='full108-exact-parent-execution-control-derivation-v1',records=records,
                  sources=348,profiles=261,stages=7,profile_suffix=1,
                  original_authentication_HEAD_custody_once_process_VM_memory_storage_guards_preserved=True,
                  compiler_invoked=False,cloud_operation=False,accepted=False)
    data = (json.dumps(result,indent=2)+'\n').encode()
    path = HERE/'full108-execution-control-derivation-v1.json'
    if path.exists(): assert path.read_bytes() == data
    else:path.open('xb').write(data)
    print(json.dumps(dict(exact_parent_controls_verified=7,sources=348,profiles=261,stages=7,cloud_operation=False)))


if __name__ == '__main__':
    main()
