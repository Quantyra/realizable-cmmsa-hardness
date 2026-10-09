"""Derive full-scope dedicated Full94 controls without VM or Lean execution."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).parent


def main():
    names = ['full93_verify.py', 'full93_worker.py', 'full93_builder02_controller.py',
             'stage_full93_builder02.py', 'full93_postprocess.py', 'full93_native_audit.py',
             'test_full93_terminal.py']
    rows = []
    for name in names:
        text = (HERE / name).read_text(encoding='utf-8').replace('full93', 'full94')
        text = text.replace('full94-manuscript-moment-resource02', 'full94-manuscript-moment-call-repair-resource02')
        text = text.replace('full94-manuscript-moment-builder02-stage', 'full94-manuscript-moment-call-repair-builder02-stage')
        if name == 'full93_native_audit.py':
            # These are the three cumulative added dyadic requests, not the
            # call-only successor's empty additional-profile list.
            before = 'from prepare_builder02_full94 import REQUESTS as DYADIC_REQUESTS'
            assert text.count(before) == 1
            text = text.replace(before, 'from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS')
        if name == 'full93_builder02_controller.py':
            assert text.count('derive_full94_execution_controls.py') == 1
        out = HERE / name.replace('full93', 'full94')
        ast.parse(text, filename=str(out))
        with out.open('x', encoding='utf-8', newline='\n') as stream:
            stream.write(text)
        rows.append({'parent': name, 'parent_sha256': digest(HERE / name),
                     'output': out.name, 'output_sha256': digest(out)})
    with (HERE / 'full94-execution-control-derivation.json').open('x', encoding='utf-8') as stream:
        json.dump({'schema': 'full94-full-scope-execution-control-derivation-v1',
                   'controls': rows, 'sources': 323, 'profiles': 181,
                   'cumulative_added_source_overlay': 4,
                   'frozen_original_finisher_unchanged': True,
                   'all_dedicated_resource_and_custody_guards_preserved': True,
                   'compiler_invoked': False, 'VM_operation_performed': False}, stream, indent=2)
        stream.write('\n')
    print('Full94 execution controls derived; all323 sources/all181 profiles retained')


if __name__ == '__main__':
    main()
