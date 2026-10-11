"""Derive full-scope Full110 GCP controls from pinned parent bytes; never execute them."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
PARENT_COMMIT = '1335b30f'
PARENT_TAG = 'full109-exact-crosslevel-warning-repair'
TAG = 'full110-exact-real-complex-operators'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def write_exact(path, data):
    if path.exists():
        assert path.read_bytes() == data, 'Derived control drift: ' + path.name
    else:
        path.open('xb').write(data)


def main():
    sources = ['full109_builder02_controller.py', 'full109_worker.py', 'full109_verify.py',
               'full109_postprocess.py', 'full109_native_audit.py', 'stage_full109_builder02.py',
               'test_full109_terminal.py', 'terminate_full109_builder02_after_custody.py']
    records = []
    for name in sources:
        raw = (HERE / name).read_bytes()
        assert raw == subprocess.check_output(['git', '-C', str(REPO), 'cat-file', 'blob',
                                               PARENT_COMMIT + ':' + PREFIX + name])
        text = raw.decode('utf-8')
        changes = []

        def replace(old, new, count=None):
            nonlocal text
            found = text.count(old)
            assert found > 0 and (count is None or found == count), (name, old, found, count)
            before = sha(text.encode())
            text = text.replace(old, new)
            changes.append(dict(old=old, new=new, occurrences=found,
                                before_sha256=before, after_sha256=sha(text.encode())))

        if PARENT_TAG in text:
            replace(PARENT_TAG, TAG)
        if 'full109' in text:
            replace('full109', 'full110')
        if 'Full109' in text:
            replace('Full109', 'Full110')
        if 'Full261' in text:
            replace('Full261', 'Full347')
        if name == 'full109_builder02_controller.py':
            old = next(line for line in text.splitlines() if line.startswith('EXTRA_LOCAL_CONTROLS = '))
            controls = ('full110_capture_gates.py', 'prepare_builder02_full110.py',
                        'full110_native_audit.py', 'full110_postprocess.py',
                        'derive_full110_execution_controls.py', 'prepare_complete_operator_scope_v2.py',
                        'prepare_full101_warning_repair.py', 'prepare_full101_spectral_application.py',
                        'recover_existing_spectral_candidate.py')
            replace(old, 'EXTRA_LOCAL_CONTROLS = ' + repr(controls), 1)
            replace("remote['project_sources_verified'] != 348", "remote['project_sources_verified'] != 369", 1)
            replace("len(manifest['requested_axioms']) != 261", "len(manifest['requested_axioms']) != 347", 1)
        if name == 'full109_verify.py':
            replace("len(manifest['project_sources']) != 348", "len(manifest['project_sources']) != 369", 1)
            replace("len(manifest['requested_axioms']) != 261", "len(manifest['requested_axioms']) != 347", 1)
            replace("manifest['requested_axioms'][-1:]", "manifest['requested_axioms'][-86:]", 1)
        if name == 'full109_postprocess.py':
            replace("    import terminate_builder02_after_custody as termination\n"
                    "    from full110_builder02_controller import audit_terminal\n"
                    "    termination.ROOT = OUTPUT\n"
                    "    termination.audit_terminal = audit_terminal\n",
                    "    import terminate_full110_builder02_after_custody as termination\n", 1)
        if name == 'full109_native_audit.py':
            replace('from prepare_builder02_full110 import REQUESTS as BRIDGE_REQUESTS',
                    'from prepare_builder02_full109 import REQUESTS as BRIDGE_REQUESTS\n'
                    '    from prepare_complete_operator_scope_v2 import additions\n'
                    '    OPERATOR_REQUESTS = additions()[1]', 1)
            replace('REQUESTS = SOURCE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS',
                    'REQUESTS = SOURCE_REQUESTS + DYADIC_REQUESTS + BRIDGE_REQUESTS + OPERATOR_REQUESTS', 1)
            replace("len(additive['added_sources']) != 29", "len(additive['added_sources']) != 50", 1)
            replace('expanded_requested_axiom_count=261', 'expanded_requested_axiom_count=347', 1)
            replace("    save(run/'material-expanded-native-report.json',expanded)",
                    "    expanded.update(exact_real_G_Phi_eigenrelation_restricted_adjoint_native_verified=expanded['full110_expanded_native_gates_green'],\n"
                    "                    exact_complex_operator_energy_eigenrelation_adjoint_native_verified=expanded['full110_expanded_native_gates_green'],\n"
                    "                    real_and_complex_two_function_Gram_native_verified=expanded['full110_expanded_native_gates_green'],\n"
                    "                    whole_complex_hypercontractivity_appendix_certified=False, full_goal_complete=False)\n"
                    "    save(run/'material-expanded-native-report.json',expanded)", 1)
        ast.parse(text, filename=name.replace('full109', 'full110'))
        rebuilt = raw.decode('utf-8')
        for change in changes:
            assert sha(rebuilt.encode()) == change['before_sha256']
            assert rebuilt.count(change['old']) == change['occurrences']
            rebuilt = rebuilt.replace(change['old'], change['new'])
            assert sha(rebuilt.encode()) == change['after_sha256']
        assert rebuilt == text
        target = name.replace('full109', 'full110')
        write_exact(HERE / target, text.encode())
        records.append(dict(source=name, source_commit=PARENT_COMMIT, source_sha256=sha(raw),
                            target=target, target_sha256=sha(text.encode()), exact_changes=changes))
    receipt = dict(schema='full110-pinned-parent-execution-control-derivation-v1', records=records,
                   project_sources=369, requested_profiles=347, stages=7,
                   added_over_full109_sources=21, added_over_full109_profiles=86,
                   cumulative_additive_sources_over_original_full83=50,
                   authentication_HEAD_custody_once_process_VM_memory_storage_guards_preserved=True,
                   postprocess_uses_explicit_full110_termination_binding=True,
                   parent_trace_and_independent_review_pending=True,
                   GCP_execution_controls_invoked=False, compiler_invoked=False,
                   cloud_operation=False, launch_clearance=False, accepted=False)
    path = HERE / 'full110-execution-control-derivation-v1.json'
    write_exact(path, (json.dumps(receipt, indent=2) + '\n').encode())
    print(json.dumps(dict(controls=len(records), sources=369, profiles=347, stages=7,
                          derivation_sha256=sha(path.read_bytes()), compiler_invoked=False,
                          cloud_operation=False, accepted=False)))


if __name__ == '__main__':
    main()
