"""Preserve exact offline capture gates and synthetic evidence tests; never Lean."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
from custody_checks import digest
from prepare_builder02_full117 import OUTPUT

HERE = Path(__file__).resolve().parent


def main():
    folder = HERE / ('full117-execution-control-validation-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    folder.mkdir(exist_ok=False)
    (folder / '.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n', encoding='utf-8')
    names = ['full117_capture_gates.py', 'prepare_builder02_full117.py', 'derive_full117_controls_v1.py', 'full117_append_block_structure_v1.py',
        'full117-control-derivation-v1.json', 'full117_builder02_controller.py', 'full117_worker.py',
        'full117_verify.py', 'full117_native_audit.py', 'full117_postprocess.py', 'stage_full117_builder02.py',
        'terminate_full117_builder02_after_custody.py', 'test_full117_terminal.py', 'test_full117_full_scope_terminal_v2.py',
        'run_full117_resume_step_v1.py', Path(__file__).name]
    for name in names:
        (folder / name).open('xb').write((HERE / name).read_bytes())
    temp = OUTPUT / 'offline-synthetic-test-temp-v2'
    temp.mkdir(exist_ok=False)
    assert temp.resolve(strict=True).is_relative_to(OUTPUT.resolve(strict=True))
    cases = ["import sys;sys.path.insert(0,sys.argv[1]);import full115_cumulative_actual_receipts_v1 as a;a.activate();import full117_capture_gates as g;g.validate_successor()",
        "import sys,tempfile,unittest;from pathlib import Path;sys.path.insert(0,sys.argv[1]);import full115_cumulative_actual_receipts_v1 as a;a.activate();p=Path(sys.argv[2]).resolve(strict=True);assert p.is_relative_to(Path(sys.argv[3]).resolve(strict=True));tempfile.tempdir=str(p);s=unittest.defaultTestLoader.loadTestsFromNames(['test_full117_terminal','test_full117_full_scope_terminal_v2']);r=unittest.TextTestRunner(verbosity=2).run(s);sys.exit(0 if r.wasSuccessful() else 1)"]
    commands = []
    for number, code in enumerate(cases):
        argv = [sys.executable, '-B', '-X', 'utf8', '-c', code, str(HERE), str(temp), str(OUTPUT)]
        with (folder / f'{number}.stdout').open('xb') as out, (folder / f'{number}.stderr').open('xb') as err:
            child = subprocess.Popen(argv, cwd=HERE, stdout=out, stderr=err, creationflags=subprocess.CREATE_NO_WINDOW)
            record = dict(argv=argv, pid=child.pid)
            commands.append(record)
            (folder / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
            while True:
                try:
                    code = child.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    print(json.dumps(dict(folder=str(folder), original_validation_process_live=child.pid)), flush=True)
        record.update(native_exit=code, stdout_sha256=digest(folder / f'{number}.stdout'), stderr_sha256=digest(folder / f'{number}.stderr'))
        (folder / 'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
        assert code == 0, 'Offline validation failed; preserve exact controls and streams'
    result = dict(commands=commands, source_snapshots={name:digest(folder / name) for name in names},
        full369_full347_seven_stage_capture_verified=True, synthetic_tests_not_native_evidence=True,
        compiler_invoked=False, cloud_operation=False, launch_clearance=False, accepted=False)
    (folder / 'result.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(folder=str(folder), all_offline_checks_passed=True, compiler_invoked=False)), flush=True)


if __name__ == '__main__':
    main()
