"""Derive dedicated lifecycle and transport controls from settled parent bytes."""
import ast
import json
from pathlib import Path
import re
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = 'c56efdcb'


def main():
    records = []
    def derive(name, target, replacements):
        raw = (HERE / name).read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', BASE + ':' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8'); changes = []
        for old, new in replacements:
            count = text.count(old)
            assert count, (name, old)
            text = text.replace(old, new)
            changes.append(dict(old=old, new=new, occurrences=count))
        ast.parse(text)
        (HERE / target).open('xb').write(text.encode('utf-8'))
        records.append(dict(source=name, source_commit=BASE, source_sha256=digest(HERE / name),
            target=target, target_sha256=digest(HERE / target), exact_replacements=changes))

    derive('run_full111_settled_cache_recovery_v1.py', 'run_full112_settled_cache_recovery_v1.py', [
        ('full112-exact-real-complex-operators-repair2', 'full113-exact-real-complex-operators-repair3'),
        ('full111', 'full112'),
        ('cmmsa_a8_output_20261011T035621Z_498f7ba6', 'cmmsa_a8_output_20261011T051406Z_3ef6ddc2'),
        ("assert action in ('boot', 'plan', 'execute', 'collect-plan', 'collect-receipt')", "assert action == 'boot', 'This derived control is admitted only for the once-guarded boot'")])
    derive('full112_dedicated_openssh_v2.py', 'full113_dedicated_openssh_v2.py', [
        ('from full111_builder02_controller import VM, VM_ID', 'from full113_builder02_controller import VM, VM_ID')])
    derive('full112_openssh_control_v1.py', 'full113_openssh_control_v1.py', [('full112', 'full113')])
    derive('terminate_full112_after_custody_openssh_v1.py', 'terminate_full113_after_custody_openssh_v1.py', [('full112', 'full113')])
    source = (HERE / 'run_full112_resume_step_v8.py').read_text(encoding='utf-8')
    old = re.search(r'^ALLOWED = .+$', source, re.M).group()
    names = ['run_full112_settled_cache_recovery_v1.py', 'run_full113_cache_recovery_v1.py',
        'audit_full113_cache_recovery_v1.py', 'preserve_full113_recovery_v1.py',
        'stage_full113_after_recovery_openssh_v1.py', 'run_full113_native_openssh_v1.py',
        'terminate_full113_after_custody_openssh_v1.py', 'full113_postprocess.py',
        'inspect_full113_recovery_capacity_v1.py', 'preserve_full113_frozen_package_v1.py']
    derive('run_full112_resume_step_v8.py', 'run_full113_resume_step_v2.py', [
        (old, 'ALLOWED = ' + repr(set(names))),
        ('from full112_builder02_controller import ROOT', 'from full113_builder02_controller import ROOT')])
    (HERE / 'full113-lifecycle-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(dict(
        records=records, VM_creation=False, other_VM_modified=False, threshold_changes=False,
        compiler_invoked=False, boot_performed=False, original_failed_operations_replayed=False), indent=2) + '\n')
    print(json.dumps(dict(controls=len(records), cloud_invoked=False)), flush=True)


if __name__ == '__main__':
    main()
