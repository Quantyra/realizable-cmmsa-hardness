"""Admit narrowly selected generated dependency artifacts with unchanged byte guards."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    records = []
    def derive(name, target, replacements):
        raw = (HERE / name).read_bytes(); text = raw.decode('utf-8'); changes = []
        for old, new in replacements:
            count = text.count(old); assert count, (name, old)
            text = text.replace(old, new); changes.append(dict(old=old, new=new, occurrences=count))
        ast.parse(text); (HERE / target).open('xb').write(text.encode('utf-8'))
        records.append(dict(source=name, source_sha256=digest(HERE / name), target=target,
            target_sha256=digest(HERE / target), exact_replacements=changes))
    old = "            assert path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ilean'))\n            assert {'.lake', 'build', 'lib', 'lean'} <= set(path.parts)"
    new = """            if scope['kind'] in ('lean-large', 'lean-small'):
                assert path.name.endswith(('.olean', '.olean.private', '.olean.server', '.ilean'))
                assert {'.lake', 'build', 'lib', 'lean'} <= set(path.parts)
                assert (row['bytes'] >= 65536) if scope['kind'] == 'lean-large' else (0 < row['bytes'] < 65536)
            else:
                assert scope['kind'] == 'generated' and row['bytes'] >= 65536
                generated_ir = {'.lake', 'build', 'ir'} <= set(path.parts) and path.name.endswith(('.c', '.c.o.export', '.setup.json'))
                generated_lean_ir = {'.lake', 'build', 'lib', 'lean'} <= set(path.parts) and path.name.endswith('.ir')
                generated_bin = path.as_posix() in ('batteries/.lake/build/bin/runLinter', 'mathlib/.lake/build/bin/cache')
                assert generated_ir or generated_lean_ir or generated_bin"""
    derive('run_full113_cache_recovery_v1.py', 'run_full113_cache_recovery_v2.py', [(old, new)])
    derive('audit_full113_cache_recovery_v1.py', 'audit_full113_cache_recovery_v2.py', [
        ('run_full113_cache_recovery_v1', 'run_full113_cache_recovery_v2'),
        ('complete-audit-v1', 'complete-audit-v2'),
        ('full113-selected-settled-cache-recovery-audit-v1', 'full113-selected-settled-cache-recovery-audit-v2')])
    derive('stage_full113_after_recovery_openssh_v1.py', 'stage_full113_after_recovery_openssh_v2.py', [
        ('audit_full113_cache_recovery_v1', 'audit_full113_cache_recovery_v2')])
    derive('preserve_full113_recovery_v1.py', 'preserve_full113_recovery_v2.py', [
        ('run_full113_cache_recovery_v1', 'run_full113_cache_recovery_v2'),
        ('audit_full113_cache_recovery_v1', 'audit_full113_cache_recovery_v2'),
        ("'inspect_full113_recovery_capacity_v2.py',", "'inspect_full113_recovery_capacity_v2.py', 'inspect_full113_generated_cache_capacity_v1.py',"),
        ("ROOT / 'capacity-inspections-v2'):", "ROOT / 'capacity-inspections-v2', ROOT / 'generated-capacity-inspections-v1'):"),
        ('full113-complete-recovery-phase-custody-v1', 'full113-complete-recovery-phase-custody-v2')])
    derive('validate_full113_openssh_controls_v1.py', 'validate_full113_openssh_controls_v2.py', [
        ('stage_full113_after_recovery_openssh_v1', 'stage_full113_after_recovery_openssh_v2'),
        ('audit_full113_cache_recovery_v1', 'audit_full113_cache_recovery_v2'),
        ('full113-openssh-control-validation-', 'full113-openssh-control-validation-v2-')])
    additions = ['run_full113_cache_recovery_v2.py', 'audit_full113_cache_recovery_v2.py',
        'stage_full113_after_recovery_openssh_v2.py', 'preserve_full113_recovery_v2.py']
    needle = "'inspect_full113_generated_cache_capacity_v1.py'"
    derive('run_full113_resume_step_v4.py', 'run_full113_resume_step_v5.py', [(needle, needle + ', ' + ', '.join(repr(n) for n in additions))])
    (HERE / 'full113-generated-recovery-controls-derivation-v2.json').open('x').write(json.dumps(dict(
        records=records, new_artifact_scope='Only paired hash-identical generated dependency build artifacts under .lake/packages',
        no_Lean_source_or_project_artifact_change=True, no_canonical_cache_write=True,
        all_once_terminal_archive_source_quiescence_and_byte_guards_preserved=True,
        minimum_disk_GiB=40, minimum_local_MiB=1536, compiler_invoked=False), indent=2) + '\n')
    print(json.dumps(dict(derived=len(records), compiler_invoked=False)), flush=True)


if __name__ == '__main__':
    main()
