"""Derive Full113 controls with exact replacements; preserve all scope and gates."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = 'c56efdcb'


def main():
    rows = []
    common = [('full112-exact-real-complex-operators-repair2', 'full113-exact-real-complex-operators-repair3'),
              ('full112', 'full113'), ('Full112', 'Full113')]
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
        target = HERE / name.replace('full112', 'full113')
        ast.parse(text, filename=target.name)
        target.open('xb').write(text.encode('utf-8'))
        rows.append(dict(source=name, source_commit=BASE, source_sha256=digest(source),
            target=target.name, target_sha256=digest(target), exact_replacements=replacements))

    gl = HERE / 'full113-rectangular-gl-repair-capture-v1'
    cx = HERE / 'full113-complex-append-repair-capture-v1'
    assert digest(gl / 'index.json') == 'E91CDE01AAFF8BD166712B50FBB960E6390515BBE9F4540A8BB8AF57CFB0E43B'
    assert digest(cx / 'index.json') == 'C21EE7445B1719E735CF7B028487FD0FA4A5337D8D8256851A4BA7549EFF91D9'
    derive('prepare_builder02_full112.py', common + [
        ('full111', 'full112'), ('Full111', 'Full112'),
        ('full113-rectangular-gl-repair-capture-v2', gl.name),
        ('52C59C2F075D3E98847D59B08819F1A33080CEE2F0C02249E05F49B0B45EBB2F', digest(gl / 'index.json')),
        ('full113-phi-repair-capture-v1', cx.name),
        ('45571240BC2B88D69BB3127BB4D7178602B7E89C6E56B1C2826A91EFE1B794C8', digest(cx / 'index.json')),
        ('ExactPhiEigenrelation.lean', 'ExactComplexAppendContinuation.lean'),
        ('cmmsa_a8_output_20261011T035621Z_498f7ba6', 'cmmsa_a8_output_20261011T051406Z_3ef6ddc2'),
        ('gl-and-phi-body-repair', 'gl-and-complex-append-body-repair')])
    derive('full112_capture_gates.py', common + [('full111', 'full112'), ('Full111', 'Full112')])
    package_rows = rows[:]
    names = ['full112_builder02_controller.py', 'full112_worker.py', 'full112_verify.py',
        'full112_postprocess.py', 'full112_native_audit.py', 'stage_full112_builder02.py',
        'test_full112_terminal.py', 'test_full112_full_scope_terminal_v2.py',
        'terminate_full112_builder02_after_custody.py', 'run_full112_resume_step_v1.py',
        'validate_full112_execution_controls_v1.py']
    for name in names:
        changes = list(common)
        if name in ('full112_builder02_controller.py', 'validate_full112_execution_controls_v1.py'):
            changes.append(('derive_full113_execution_controls.py', Path(__file__).name))
        derive(name, changes)
    metadata = dict(source_count=369, requests=347, stages=7, archive_members=376,
        other_source_bodies_preserved=367, all_parent_thresholds_retained=True,
        GCP_only=True, unchanged_local_reserve_MiB=1536, unchanged_remote_disk_GiB=40,
        unchanged_remote_RAM_GiB=48, compiler_invoked=False, package_prepared=False, launch_clearance=False)
    for suffix, subset in [('package', package_rows), ('execution', rows[2:])]:
        result = dict(schema='full113-two-body-' + suffix + '-control-derivation-v1', records=subset, **metadata)
        (HERE / ('full113-' + suffix + '-control-derivation-v1.json')).open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(controls=len(rows), compiler_invoked=False)))


if __name__ == '__main__':
    main()
