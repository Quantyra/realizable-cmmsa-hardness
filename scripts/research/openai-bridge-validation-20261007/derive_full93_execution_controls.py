"""Derive dedicated Full93 controls from pinned Full92 controls, without execution."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).parent
NAMES = ['full92_verify.py', 'full92_worker.py', 'full92_builder02_controller.py',
         'stage_full92_builder02.py', 'full92_postprocess.py', 'full92_native_audit.py']


def replace(text, before, after, count=1):
    assert text.count(before) == count, (before, text.count(before))
    return text.replace(before, after)


def main():
    rows = []
    for name in NAMES:
        text = (HERE / name).read_text(encoding='utf-8')
        text = text.replace('full92', 'full93')
        text = text.replace('full93-source-size-profile-resource02', 'full93-manuscript-moment-resource02')
        text = text.replace('full93-source-size-profile-builder02-stage', 'full93-manuscript-moment-builder02-stage')
        if name == 'full92_verify.py':
            text = replace(text, "len(manifest['project_sources']) != 322 or len(manifest['requested_axioms']) != 178 or manifest['requested_axioms'][-5:]", "len(manifest['project_sources']) != 323 or len(manifest['requested_axioms']) != 181 or manifest['requested_axioms'][-3:]")
        if name == 'full92_builder02_controller.py':
            text = replace(text, 'Full178 standard-axiom', 'Full181 standard-axiom')
            text = replace(text, "'full93_postprocess.py')", "'full93_postprocess.py','derive_full93_execution_controls.py')")
            text = replace(text, "if remote['auxiliary_inputs_verified']", "if remote['project_sources_verified'] != 323: raise RuntimeError('Incomplete project source verification')\n    if len(manifest['requested_axioms']) != 181: raise RuntimeError('Incomplete profile scope')\n    if remote['auxiliary_inputs_verified']")
        if name == 'full92_native_audit.py':
            # Keep Full90 as the base material-expansion repair, independently
            # of the Full93 direct parent Full92.
            text = replace(text, 'from prepare_builder02_full91 import PARENT, REQUESTS',
                           'from prepare_builder02_full91 import PARENT, REQUESTS as SOURCE_REQUESTS\n    from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS\n    REQUESTS = SOURCE_REQUESTS + DYADIC_REQUESTS')
            text = replace(text, "original=json.loads((cap/'inputs/capture-manifest.json').read_bytes())",
                           "original=json.loads((cap/'inputs/capture-manifest.json').read_bytes())\n    additive = dict(additive)\n    additive['added_sources'] = sorted(set(inner['project_sources']) - set(original['project_sources']))\n    if len(additive['added_sources']) != 4: raise RuntimeError('Incomplete cumulative additive source scope')")
            text = replace(text, 'expanded_requested_axiom_count=178', 'expanded_requested_axiom_count=181')
            text = replace(text, 'source_row_independence_native_verified=not extra_bad)',
                           'source_row_independence_native_verified=not extra_bad, manuscript_dyadic_consumer_native_verified=not extra_bad, numeric_NO_proven=False)')
        output = HERE / name.replace('full92', 'full93')
        ast.parse(text, filename=str(output))
        with output.open('x', encoding='utf-8', newline='\n') as stream:
            stream.write(text)
        rows.append({'parent': name, 'parent_sha256': digest(HERE / name),
                     'output': output.name, 'output_sha256': digest(output)})
    receipt = {'schema': 'full93-execution-control-derivation-v1', 'controls': rows,
               'project_sources': 323, 'requested_profiles': 181,
               'cumulative_added_source_overlay': 4,
               'original_finisher_sha256': 'AE79CB1B154685AF9DB0E43885225F49C7EB750C5F6F5A8D2B5595ED3EEE7156',
               'VM': 'quantyra-lean-builder-02', 'VM_ID': '7237681467779354904',
               'local_compilation': False, 'launch_called': False,
               'guards_preserved': ['frozen_capture_HEAD_context', 'logical136_preservation',
                   'source_config_compiler_package_core_cache', 'auth_exact_dedicated_VM',
                   'no_external_IP', 'memory48GiB', 'remote_disk40GiB',
                   'local_custody_reserve1536MiB', 'no_existing_Lean_Lake',
                   'idle_shutdown_timer', 'exclusive_launch_markers',
                   'native_stage_and_full_profile_scope', 'two_copy_custody',
                   'termination_after_terminal_and_quiescence']}
    with (HERE / 'full93-execution-control-derivation.json').open('x', encoding='utf-8') as stream:
        json.dump(receipt, stream, indent=2)
        stream.write('\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
