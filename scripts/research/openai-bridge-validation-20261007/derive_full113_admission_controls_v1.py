"""Bind frozen-package preservation and transport controls to exact validation."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = 'c56efdcb'
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
VALIDATION = 'full113-execution-control-validation-20261011T053328425826Z'


def main():
    result = json.loads((HERE / VALIDATION / 'result.json').read_bytes())
    assert all(row['native_exit'] == 0 for row in result['commands'])
    assert 'Ran 16 tests' in (HERE / VALIDATION / '1.stderr').read_text()
    records = []
    items = [
        ('preserve_full112_frozen_package_v1.py', 'preserve_full113_frozen_package_v1.py', [
            ('full112', 'full113'),
            ('full113-execution-control-validation-20261011T043143761793Z', VALIDATION),
            ('original_preparation_tool_handle=86509', 'original_preparation_tool_handle=74402'),
            ('original_validation_tool_handle=91702', 'original_validation_tool_handle=74402')]),
        ('run_full112_native_openssh_v1.py', 'run_full113_native_openssh_v1.py', [
            ('full112', 'full113'), ('Full112', 'Full113'),
            ('full113-execution-control-validation-20261011T043143761793Z', VALIDATION)]),
        ('stage_full112_after_recovery_openssh_v4.py', 'stage_full113_after_recovery_openssh_v1.py', [
            ('full112', 'full113'), ('audit_full111_settled_cache_recovery_v4', 'audit_full113_cache_recovery_v1'),
            ('eight-scope', 'selected-scope'), ('all_eight_recovery_scopes_verified', 'all_selected_recovery_scopes_verified')]),
        ('validate_full112_openssh_controls_v1.py', 'validate_full113_openssh_controls_v1.py', [
            ('full112', 'full113'),
            ('stage_full113_after_recovery_openssh_v2.py', 'stage_full113_after_recovery_openssh_v1.py'),
            ('audit_full111_settled_cache_recovery_v2.py', 'audit_full113_cache_recovery_v1.py')]),
    ]
    for name, target, replacements in items:
        raw = (HERE / name).read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', BASE + ':' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8'); changes = []
        for old, new in replacements:
            count = text.count(old); assert count, (name, old)
            text = text.replace(old, new); changes.append(dict(old=old, new=new, occurrences=count))
        ast.parse(text)
        (HERE / target).open('xb').write(text.encode('utf-8'))
        records.append(dict(source=name, source_commit=BASE, source_sha256=digest(HERE / name),
            target=target, target_sha256=digest(HERE / target), exact_replacements=changes))
    (HERE / 'full113-admission-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(dict(
        records=records, validation_result_sha256=digest(HERE / VALIDATION / 'result.json'),
        no_threshold_or_acceptance_gate_change=True, compiler_invoked=False, cloud_invoked=False), indent=2) + '\n')
    print(json.dumps(dict(controls=len(records), validation=VALIDATION)), flush=True)


if __name__ == '__main__':
    main()
