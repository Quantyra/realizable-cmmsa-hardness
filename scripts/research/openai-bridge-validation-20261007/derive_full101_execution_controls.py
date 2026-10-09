"""Derive exact Full100 execution algorithms with explicit additive scope bindings."""
import ast
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).parent
PARENT_TAG = 'full100-matrix-fourier-bullet-repair'
TAG = 'full101-spectral-original-application'
NAMES = ['full100_verify.py', 'full100_worker.py', 'full100_builder02_controller.py',
         'stage_full100_builder02.py', 'full100_postprocess.py', 'full100_native_audit.py',
         'test_full100_terminal.py']


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def expected(name):
    original = (HERE / name).read_bytes()
    text = original.decode('utf-8').replace(PARENT_TAG, TAG).replace('full100', 'full101')
    changes = []

    def change(old, new):
        nonlocal text
        assert text.count(old) == 1, (name, old)
        text = text.replace(old, new)
        changes.append(dict(old=old, new=new))

    if name == 'full100_verify.py':
        change("len(manifest['project_sources']) != 327 or len(manifest['requested_axioms']) != 192 or manifest['requested_axioms'][-8:]",
               "len(manifest['project_sources']) != 340 or len(manifest['requested_axioms']) != 251 or manifest['requested_axioms'][-59:]")
    if name in ['full100_builder02_controller.py', 'test_full100_terminal.py']:
        change('Full192 standard-axiom scope', 'Full251 standard-axiom scope')
    if name == 'full100_builder02_controller.py':
        change("remote['project_sources_verified'] != 327", "remote['project_sources_verified'] != 340")
        change("len(manifest['requested_axioms']) != 192", "len(manifest['requested_axioms']) != 251")
        change("'derive_full101_execution_controls.py','prepare_full101_bullet_candidates.py')",
               "'derive_full101_execution_controls.py','prepare_full101_spectral_application.py','recover_existing_spectral_candidate.py')")
        # Relative candidate files are separately pinned through capture gates;
        # the required preparer replaces the syntax-only predecessor's validator.
    if name == 'full100_native_audit.py':
        change("len(additive['added_sources']) != 8", "len(additive['added_sources']) != 21")
        change("normalized['stages'][4]=original['stages'][4]",
               "normalized['stages'][4]=original['stages'][4]\n        normalized['stages'][5]=original['stages'][5]\n        normalized['owned_sources']=original['owned_sources']\n        normalized['external_imports']=original['external_imports']")
        change('expanded_requested_axiom_count=192', 'expanded_requested_axiom_count=251')
        change('universal_Spectral47_inhabitant_proven=False)',
               "universal_Spectral47_inhabitant_proven=False, universal_Spectral47_inhabitant_native_verified=expanded['full101_expanded_native_gates_green'], actual_selected_leaf_spectral_application_native_verified=expanded['full101_expanded_native_gates_green'], exact_manuscript_eigenvalue_and_G_Phi_laws_closed=False)")
    ast.parse(text)
    return text.encode('utf-8'), dict(source=name, source_sha256=sha(original),
        target=name.replace('full100', 'full101'), target_sha256=sha(text.encode('utf-8')),
        path_module_binding_replacements={PARENT_TAG: TAG, 'full100': 'full101'}, explicit_scope_changes=changes)


def main(write=False):
    records = []
    for name in NAMES:
        data, record = expected(name)
        target = HERE / record['target']
        if write:
            with target.open('xb') as stream:
                stream.write(data)
        else:
            assert target.read_bytes() == data
        records.append(record)
    result = dict(schema='full101-exact-parent-execution-control-derivation-v1', records=records,
        source_scope=340, required_profiles=251, inherited_sources=327, inherited_profiles=192,
        new_profile_suffix=59, cumulative_added_sources=21, seven_stages_preserved=True,
        authentication_storage_memory_process_network_idle_exclusive_custody_termination_algorithms_preserved=True,
        manuscript_and_runtime_obligations_remain_open=True, compiler_invoked=False, cloud_operation=False,
        launch_clearance=False, accepted=False)
    data = (json.dumps(result, indent=2) + '\n').encode()
    p = HERE / 'full101-execution-control-derivation.json'
    if write:
        with p.open('xb') as stream:
            stream.write(data)
    elif sys.argv[1:] == ['--refresh-record']:
        # Offered initial unexecuted record is retained before a static correction.
        preserved = HERE / 'full101-control-preparation-correction-v1' / p.name
        assert preserved.read_bytes() == p.read_bytes()
        p.write_bytes(data)
    else:
        assert p.read_bytes() == data
    print('Seven Full101 controls preserve parent algorithms and explicit full340/full251 scope')


if __name__ == '__main__':
    assert sys.argv[1:] in ([], ['--write'], ['--refresh-record'])
    main(sys.argv[1:] == ['--write'])
