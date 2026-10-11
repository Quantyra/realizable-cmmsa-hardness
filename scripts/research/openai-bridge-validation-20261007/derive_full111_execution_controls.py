"""Derive the unchanged full-scope GCP gates for the two-source repair capsule."""
import ast
import json
from pathlib import Path
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = '02e43c58'


def main():
    names = ['full110_builder02_controller.py', 'full110_worker.py', 'full110_verify.py',
        'full110_postprocess.py', 'full110_native_audit.py', 'stage_full110_builder02.py',
        'test_full110_terminal.py', 'test_full110_full_scope_terminal_v2.py',
        'terminate_full110_builder02_after_custody.py', 'run_full110_resume_step_v1.py']
    records = []
    for name in names:
        source = HERE / name
        raw = source.read_bytes()
        assert raw == subprocess.check_output(['git', 'cat-file', 'blob', BASE + ':' + PREFIX + name], cwd=REPO)
        text = raw.decode('utf-8')
        changes = []

        def replace(old, new):
            nonlocal text
            count = text.count(old)
            assert count > 0, (name, old)
            text = text.replace(old, new)
            changes.append(dict(old=old, new=new, occurrences=count))

        if 'full110-exact-real-complex-operators' in text:
            replace('full110-exact-real-complex-operators', 'full111-exact-real-complex-operators-repair')
        if 'full110' in text:
            replace('full110', 'full111')
        if 'Full110' in text:
            replace('Full110', 'Full111')
        if name == 'test_full110_full_scope_terminal_v2.py':
            replace("added_path = self.binding['added_files'][-1]", "added_path = 'lean/PvNP/RealizableHardness/ExactPhiEigenrelation.lean'")
        target = HERE / name.replace('full110', 'full111')
        ast.parse(text, filename=target.name)
        rebuilt = raw.decode('utf-8')
        for row in changes:
            assert rebuilt.count(row['old']) == row['occurrences']
            rebuilt = rebuilt.replace(row['old'], row['new'])
        assert rebuilt == text
        target.open('xb').write(text.encode('utf-8'))
        records.append(dict(source=name, source_commit=BASE, source_sha256=digest(source),
            target=target.name, target_sha256=digest(target), exact_replacements=changes))
    receipt = dict(schema='full111-source-repair-execution-control-derivation-v1', records=records,
        sources=369, requests=347, stages=7, all_parent_thresholds_retained=True,
        first_fixture_source_drift_targets_repaired_phi=True,
        GCP_only=True, unchanged_local_reserve_MiB=1536, unchanged_remote_disk_GiB=40,
        unchanged_remote_RAM_GiB=48, compiler_invoked=False, launch_clearance=False)
    (HERE / 'full111-execution-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(dict(controls=len(records), compiler_invoked=False, launch_clearance=False)))


if __name__ == '__main__':
    main()
