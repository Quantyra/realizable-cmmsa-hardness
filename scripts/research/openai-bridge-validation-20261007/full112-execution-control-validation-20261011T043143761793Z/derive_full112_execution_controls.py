"""Derive unchanged full369/full347 controls for the next two-body repair."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = '4930801c'


def main():
    records = []
    names = ['full111_builder02_controller.py', 'full111_worker.py', 'full111_verify.py',
        'full111_postprocess.py', 'full111_native_audit.py', 'stage_full111_builder02.py',
        'test_full111_terminal.py', 'test_full111_full_scope_terminal_v2.py',
        'terminate_full111_builder02_after_custody.py', 'run_full111_resume_step_v1.py',
        'validate_full111_execution_controls_v1.py']
    for name in names:
        source = HERE / name
        raw = source.read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', BASE + ':' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8')
        changes = []
        for old, new in [
            ('full111-exact-real-complex-operators-repair', 'full112-exact-real-complex-operators-repair2'),
            ('full111', 'full112'), ('Full111', 'Full112')]:
            count = text.count(old)
            if count:
                text = text.replace(old, new)
                changes.append(dict(old=old, new=new, occurrences=count))
        target = HERE / name.replace('full111', 'full112')
        ast.parse(text, filename=target.name)
        target.open('xb').write(text.encode('utf-8'))
        records.append(dict(source=name, source_commit=BASE, source_sha256=digest(source),
            target=target.name, target_sha256=digest(target), exact_replacements=changes))
    result = dict(schema='full112-source-repair-execution-control-derivation-v1', records=records,
        sources=369, requests=347, stages=7, all_parent_thresholds_retained=True,
        GCP_only=True, unchanged_local_reserve_MiB=1536, unchanged_remote_disk_GiB=40,
        unchanged_remote_RAM_GiB=48, compiler_invoked=False, launch_clearance=False)
    (HERE / 'full112-execution-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(derived_controls=len(records), compiler_invoked=False)))


if __name__ == '__main__':
    main()
