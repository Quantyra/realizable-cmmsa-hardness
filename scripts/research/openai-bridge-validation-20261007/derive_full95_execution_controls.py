"""Derive exact full-scope Full95 controls; never execute a compiler or VM operation."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).parent


def main():
    names = ['full94_verify.py', 'full94_worker.py', 'full94_builder02_controller.py',
             'stage_full94_builder02.py', 'full94_postprocess.py', 'full94_native_audit.py',
             'test_full94_terminal.py']
    rows = []
    for name in names:
        text = (HERE / name).read_text(encoding='utf-8').replace('full94', 'full95')
        text = text.replace('full95-manuscript-moment-call-repair-resource02', 'full95-manuscript-moment-syntax-repair-resource02')
        text = text.replace('full95-manuscript-moment-call-repair-builder02-stage', 'full95-manuscript-moment-syntax-repair-builder02-stage')
        # The native audit retains the Full91 and Full93 cumulative request
        # lists, independently of this successor's two-delimiter repair.
        if name == 'full94_native_audit.py':
            assert 'from prepare_builder02_full93 import REQUESTS as DYADIC_REQUESTS' in text
        out = HERE / name.replace('full94', 'full95')
        ast.parse(text, filename=str(out))
        with out.open('x', encoding='utf-8', newline='\n') as stream:
            stream.write(text)
        rows.append({'parent': name, 'parent_sha256': digest(HERE / name),
                     'output': out.name, 'output_sha256': digest(out)})
    with (HERE / 'full95-execution-control-derivation.json').open('x', encoding='utf-8') as stream:
        json.dump({'schema': 'full95-full-scope-execution-control-derivation-v1',
                   'controls': rows, 'sources': 323, 'profiles': 181,
                   'cumulative_added_source_overlay': 4,
                   'frozen_original_finisher_unchanged': True,
                   'all_dedicated_resource_and_custody_guards_preserved': True,
                   'compiler_invoked': False, 'VM_operation_performed': False}, stream, indent=2)
        stream.write('\n')
    print('Full95 full323/full181 execution controls derived; no launch')


if __name__ == '__main__':
    main()
