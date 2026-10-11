"""Derive read-only recovery audit, idle refresh and existing-boot staging controls."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'


def main():
    rows = []

    def derive(source_name, target_name, changes, committed=True):
        source = HERE / source_name
        raw = source.read_bytes()
        if committed:
            assert raw == subprocess.check_output(['git', 'cat-file', 'blob', '4930801c:' + PREFIX + source_name], cwd=REPO)
        text = raw.decode('utf-8')
        records = []
        for old, new in changes:
            count = text.count(old)
            assert count > 0, (source_name, old)
            text = text.replace(old, new)
            records.append(dict(old=old, new=new, occurrences=count))
        ast.parse(text, filename=target_name)
        target = HERE / target_name
        target.open('xb').write(text.encode('utf-8'))
        rows.append(dict(parent=source_name, parent_sha256=digest(source), target=target_name,
                         target_sha256=digest(target), exact_replacements=records))

    derive('audit_full110_settled_cache_recovery_v1.py', 'audit_full111_settled_cache_recovery_v1.py', [
        ('full110', 'full111'), ('[110, 90, 91, 92, 93, 94, 95]', '[111, 96, 97, 98]'),
        ('all seven settled scopes', 'all four settled scopes'), ('all-seven', 'all-four'),
        ('all_seven_scopes_verified', 'all_four_scopes_verified')])
    derive('refresh_full110_recovery_idle_v1.py', 'refresh_full111_recovery_idle_v1.py', [
        ('full111-exact-real-complex-operators-repair-resource02', 'full112-exact-real-complex-operators-repair2-resource02'),
        ('full110', 'full111')])
    derive('run_full111_resume_step_v4.py', 'run_full111_resume_step_v5.py', [
        ("'derive_full111_settled_cache_recovery_v1.py'", "'derive_full111_settled_cache_recovery_v1.py', 'audit_full111_settled_cache_recovery_v1.py'")], committed=False)
    derive('stage_full111_after_recovery_v2.py', 'stage_full112_after_recovery_v1.py', [
        ('full111-exact-real-complex-operators-repair', 'full112-exact-real-complex-operators-repair2'),
        ('full111', 'full112'), ('Full111', 'Full112'),
        ('audit_full110_settled_cache_recovery_v2', 'audit_full111_settled_cache_recovery_v1'),
        ('all_seven_recovery_scopes_verified', 'all_four_recovery_scopes_verified')])
    result = dict(schema='full112-four-scope-recovery-audit-controls-v1', records=rows,
        exact_parent_semantics_preserved=True, minimum_remote_GiB=40,
        power_operations_by_audit_or_idle=False, compiler_invoked=False)
    (HERE / 'full112-recovery-audit-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(derived_controls=len(rows), cloud_action_performed=False)))


if __name__ == '__main__':
    main()
