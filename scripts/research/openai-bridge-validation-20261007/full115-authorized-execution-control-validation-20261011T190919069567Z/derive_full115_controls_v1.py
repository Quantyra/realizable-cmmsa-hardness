"""Derive guarded Full115 controls; preparation and all cloud actions are separate."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = 'e0b53e9baaf304c3014b625a68add6e3c82f0019'


def main():
    common = [('full114-exact-real-complex-operators-repair4', 'full115-exact-real-complex-operators-repair5'),
              ('full114', 'full115'), ('Full114', 'Full115')]
    rows = []

    def derive(name, changes):
        source = HERE / name
        raw = source.read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', BASE + ':' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8')
        replacements = []
        for old, new in changes:
            count = text.count(old)
            if not count:
                assert (old, new) in common, (name, old)
                continue
            text = text.replace(old, new)
            replacements.append(dict(old=old, new=new, occurrences=count))
        target = HERE / name.replace('full114', 'full115')
        ast.parse(text, filename=target.name)
        target.open('xb').write(text.encode('utf-8'))
        rows.append(dict(source=name, source_commit=BASE, source_sha256=digest(source),
                         target=target.name, target_sha256=digest(target), exact_replacements=replacements))

    capture = HERE / 'full115-rectangular-gl-repair-capture-v2'
    assert digest(capture / 'index.json') == 'E3984B6C3A6127511E7B64B060B61A4EE7754C0DEF1183E92BFA7509B054EF16'
    derive('prepare_builder02_full114.py', common + [
        ('full113', 'full114'), ('Full113', 'Full114'),
        ('GL private-helper repair', 'GL cardinal-instance repair'),
        ('full115-rectangular-gl-repair-capture-v1', 'full115-rectangular-gl-repair-capture-v2'),
        ('3BC555371B9FB47FF48D69DF1F65DAD74A1B10A6D63F0D11D7E8EF5892E665E1', digest(capture / 'index.json')),
        ('cmmsa_a8_output_20261011T060110Z_204d10cd', 'cmmsa_a8_output_20261011T070000Z_135b1f28'),
        ('gl-private-helper-repair', 'gl-cardinal-instance-repair'),
        ('exactly_two_reviewed_private_helpers_added=True', 'all_existing_private_helpers_preserved=True'),
        ('theorem_local_heartbeat_cap_reduced_from800000_to400000=True', 'theorem_local_heartbeat_cap_unchanged_at400000=True')])
    derive('full114_capture_gates.py', common + [('full113', 'full114'), ('Full113', 'Full114'),
                                                ('private-helper repair', 'cardinal-instance repair')])
    for name in ['full114_builder02_controller.py', 'full114_worker.py', 'full114_verify.py',
                 'full114_postprocess.py', 'full114_native_audit.py', 'stage_full114_builder02.py',
                 'test_full114_terminal.py', 'test_full114_full_scope_terminal_v2.py',
                 'terminate_full114_builder02_after_custody.py', 'run_full114_resume_step_v1.py',
                 'validate_full114_execution_controls_v1.py']:
        derive(name, common)
    metadata = dict(records=rows, sources=369, requests=347, stages=7, archive_members=376,
                    only_GL_body_changed=True, all_public_and_private_headers_preserved=True,
                    all_checks_and_options_preserved=True, all_parent_thresholds_retained=True,
                    local_reserve_MiB=1536, remote_disk_GiB=40, remote_RAM_GiB=48,
                    package_prepared=False, compiler_invoked=False, cloud_action=False, launch_clearance=False)
    (HERE / 'full115-control-derivation-v1.json').open('x').write(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps(dict(controls=len(rows), package_prepared=False, compiler_invoked=False, cloud_action=False)))


if __name__ == '__main__':
    main()
