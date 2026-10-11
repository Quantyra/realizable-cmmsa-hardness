"""Derive the single GL repair; retain every public declaration, scope and gate."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = '91ea5a69'


def main():
    rows = []
    common = [('full113-exact-real-complex-operators-repair3', 'full114-exact-real-complex-operators-repair4'),
              ('full113', 'full114'), ('Full113', 'Full114')]
    def derive(name, changes):
        source = HERE / name
        raw = source.read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', BASE + ':' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8'); replacements = []
        for old, new in changes:
            count = text.count(old)
            if not count:
                assert (old, new) in common, (name, old)
                continue
            text = text.replace(old, new)
            replacements.append(dict(old=old, new=new, occurrences=count))
        target = HERE / name.replace('full113', 'full114')
        ast.parse(text, filename=target.name)
        target.open('xb').write(text.encode('utf-8'))
        rows.append(dict(source=name, source_commit=BASE, source_sha256=digest(source),
            target=target.name, target_sha256=digest(target), exact_replacements=replacements))

    gl = HERE / 'full114-rectangular-gl-repair-capture-v1'
    assert digest(gl / 'index.json') == '3BC555371B9FB47FF48D69DF1F65DAD74A1B10A6D63F0D11D7E8EF5892E665E1'
    derive('prepare_builder02_full113.py', common + [
        ('full112', 'full113'), ('Full112', 'Full113'),
        ('Freeze the two body-only Full113 repairs', 'Freeze the one-source Full113 GL private-helper repair'),
        ('from prepare_builder02_full103 import headers', 'from full114_gl_repair_structure_v1 import validate as validate_structure'),
        ('E91CDE01AAFF8BD166712B50FBB960E6390515BBE9F4540A8BB8AF57CFB0E43B', digest(gl / 'index.json')),
        ("    ('full114-complex-append-repair-capture-v1', 'C21EE7445B1719E735CF7B028487FD0FA4A5337D8D8256851A4BA7549EFF91D9', 'ExactComplexAppendContinuation.lean'),\n", ''),
        ('assert headers(old[name]) == headers(data)', 'validate_structure(old[name], data)'),
        ('cmmsa_a8_output_20261011T051406Z_3ef6ddc2', 'cmmsa_a8_output_20261011T060110Z_204d10cd'),
        ('gl-and-complex-append-body-repair', 'gl-private-helper-repair'),
        ('all367_other_source_bytes_preserved', 'all368_other_source_bytes_preserved'),
        ('all_declaration_headers_and_imports_and_configuration_preserved=True,',
         "all_existing_declaration_headers_and_imports_preserved=True,\n        exactly_two_reviewed_private_helpers_added=True,\n        theorem_local_heartbeat_cap_reduced_from800000_to400000=True,"),
        ('project_sources_preserved=367', 'project_sources_preserved=368')])
    derive('full113_capture_gates.py', common + [('full112', 'full113'), ('Full112', 'Full113'),
        ('two-body', 'one-source private-helper')])
    package_rows = rows[:]
    names = ['full113_builder02_controller.py', 'full113_worker.py', 'full113_verify.py',
        'full113_postprocess.py', 'full113_native_audit.py', 'stage_full113_builder02.py',
        'test_full113_terminal.py', 'test_full113_full_scope_terminal_v2.py',
        'terminate_full113_builder02_after_custody.py', 'run_full113_resume_step_v1.py',
        'validate_full113_execution_controls_v1.py']
    for name in names:
        changes = list(common)
        if name == 'validate_full113_execution_controls_v1.py':
            changes.append(("'derive_full114_controls_v1.py',", "'derive_full114_controls_v1.py', 'full114_gl_repair_structure_v1.py',"))
        derive(name, changes)
    metadata = dict(source_count=369, requests=347, stages=7, archive_members=376,
        other_source_bytes_preserved=368, all_existing_declarations_preserved=True,
        exactly_two_reviewed_private_helpers=True, all_parent_thresholds_retained=True,
        GCP_only=True, unchanged_local_reserve_MiB=1536, unchanged_remote_disk_GiB=40,
        unchanged_remote_RAM_GiB=48, compiler_invoked=False, package_prepared=False, launch_clearance=False)
    for suffix, subset in [('package', package_rows), ('execution', rows[2:])]:
        result = dict(schema='full114-one-source-private-helper-' + suffix + '-control-derivation-v1', records=subset, **metadata)
        (HERE / ('full114-' + suffix + '-control-derivation-v1.json')).open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(controls=len(rows), compiler_invoked=False)))


if __name__ == '__main__':
    main()
