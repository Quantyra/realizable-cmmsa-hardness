"""Bind settled Full111 recovery to the next immutable repair; no cloud action."""
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

    def derive(source_name, target_name, changes):
        source = HERE / source_name
        raw = source.read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', 'adf1e917:' + PREFIX + source_name], cwd=REPO)
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
        rows.append(dict(parent=source_name, parent_commit='adf1e917', parent_sha256=digest(source),
                         target=target_name, target_sha256=digest(target), exact_replacements=records))

    common = [
        ('full111-exact-real-complex-operators-repair-resource02', 'full112-exact-real-complex-operators-repair2-resource02'),
        ('full111_verify.py', 'full112_verify.py'), ('full110', 'full111'), ('Full110', 'Full111')]
    derive('derive_full110_settled_cache_recovery_v1.py', 'derive_full111_settled_cache_recovery_v1.py', common + [
        ('(110, 90, 91, 92, 93, 94, 95)', '(111, 96, 97, 98)'),
        ('number == 110', 'number == 111'),
        ('target = HERE /', "if number == 111:\n            replace('TARGET = 5 * 1024**3', 'TARGET = 8 * 1024**3')\n        target = HERE /"),
        ('target_bytes=5 * 1024**3', 'target_bytes=8 * 1024**3'),
        ('seven settled runs', 'four settled runs')])
    derive('run_full110_settled_cache_recovery_v1.py', 'run_full111_settled_cache_recovery_v1.py', [
        common[0], ('full110', 'full111'),
        ('cmmsa_a8_output_20261011T025221Z_7046a7c0', 'cmmsa_a8_output_20261011T035621Z_498f7ba6')])
    derive('run_full111_resume_step_v1.py', 'run_full111_resume_step_v4.py', [
        ("ALLOWED = {'stage_full111_builder02.py', 'full111_builder02_controller.py', 'full111_postprocess.py'}",
         "ALLOWED = {'run_full111_settled_cache_recovery_v1.py', 'derive_full111_settled_cache_recovery_v1.py', 'refresh_full111_recovery_idle_v1.py'}")])
    value = dict(schema='full112-settled-parent-recovery-preparation-v1', records=rows,
        intended_scopes=[111, 96, 97, 98], intended_large_GiB=8, intended_small_MiB=896,
        same_byte_identity_and_quiescence_and_once_guards=True, source_and_project_objects_excluded=True,
        minimum_remote_GiB=40, minimum_local_MiB=1536, compiler_invoked=False, cloud_action_performed=False)
    (HERE / 'full112-recovery-preparation-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2) + '\n')
    print(json.dumps(dict(derived_controls=len(rows), cloud_action_performed=False)))


if __name__ == '__main__':
    main()
