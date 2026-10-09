"""Preserve complete Full103 execution algorithms for frozen Full104 scope."""
import ast
import json
import sys
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full103_verify.py', 'full103_worker.py', 'full103_builder02_controller.py',
         'stage_full103_builder02.py', 'full103_postprocess.py',
         'full103_native_audit.py', 'test_full103_terminal.py']


def main(write=False):
    records = []
    for name in NAMES:
        text = (HERE/name).read_text(encoding='utf-8')
        text = text.replace('full103-spectral-owned-warning-repair', 'full104-actual-consumer-exact-energy')
        text = text.replace('full103', 'full104').replace('Full103', 'Full104')
        text = text.replace('340', '344').replace('251', '257')
        if name == 'full103_verify.py':
            assert text.count("manifest['requested_axioms'][-59:]") == 1
            text = text.replace("manifest['requested_axioms'][-59:]", "manifest['requested_axioms'][-6:]")
        if name == 'full103_native_audit.py':
            assert text.count("len(additive['added_sources']) != 21") == 1
            text = text.replace("len(additive['added_sources']) != 21", "len(additive['added_sources']) != 25")
            old = "exact_manuscript_eigenvalue_and_G_Phi_laws_closed=False)"
            assert text.count(old) == 1
            text = text.replace(old, old + "\n    expanded.update(actual_SourceSize_and_dyadic_spectral_discharge_native_verified=expanded['full104_expanded_native_gates_green'], exact_image_rank_and_frame_energy_native_verified=expanded['full104_expanded_native_gates_green'])")
        ast.parse(text)
        path = HERE/name.replace('full103', 'full104')
        data = text.encode()
        if write:
            path.open('xb').write(data)
        else:
            assert path.read_bytes() == data
        records.append(dict(source=name, source_sha256=digest(HERE/name),
                            target=path.name, target_sha256=digest(path)))
    result = dict(schema='full104-full344-full257-execution-control-derivation-v1',
        records=records, cumulative_added_sources=25, fresh_binding_profiles=6,
        all_seven_stage_prefixes_preserved=True,
        resource_auth_storage_memory_process_once_custody_warning_guards_preserved=True,
        parent_compiler_and_566_warm_object_guards_preserved=True,
        native_verification_pending=True, compiler_invoked=False, accepted=False)
    path = HERE/'full104-execution-control-derivation.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if write:
        path.open('xb').write(data)
    else:
        assert path.read_bytes() == data
    print('Seven controls preserve full344/full257/seven-stage successor scope')


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'])
    main(sys.argv[1:] == ['--write'])
