"""Derive a separately guarded third recovery boot and complete-output resume wrapper."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    changes = [
        ('boot_full109_trace_recovery_v2.py', 'boot_full109_trace_recovery_v3.py', [
            ("trace/'settled-cache-recovery-boot-v1/boot-result.json'", "trace/'settled-cache-recovery-boot-v2/boot-result.json'"),
            ("folder = trace/'settled-cache-recovery-boot-v2'", "folder = trace/'settled-cache-recovery-boot-v3'"),
        ]),
        ('run_full109_resume_step_v3.py', 'run_full109_resume_step_v4.py', [
            ("    'boot_full109_trace_recovery_v2.py',", "    'boot_full109_trace_recovery_v3.py',\n    'collect_full109_native89_receipt_v1.py',\n    'audit_full109_complete_trace_recovery_v4.py',\n    'inspect_full109_trace_recovery_progress_v2.py',"),
        ]),
    ]
    rows = []
    for old, new, replacements in changes:
        source = HERE / old
        raw = source.read_bytes()
        result = raw
        for before, after in replacements:
            newline = b'\r\n' if b'\r\n' in raw else b'\n'
            left = before.encode().replace(b'\n', newline)
            right = after.encode().replace(b'\n', newline)
            assert result.count(left) == 1
            result = result.replace(left, right)
        compile(result, new, 'exec')
        target = HERE / new
        target.open('xb').write(result)
        rows.append(dict(source=old, source_sha256=digest(source), successor=new,
                         successor_sha256=digest(target), exact_replacements=replacements))
    value = dict(rows=rows, original_controls_unchanged=True, vm_start_requires_fresh_exact_TERMINATED=True,
                 frozen_capture_and_resource_gates_unchanged=True, recovery_or_compiler_replay_authorized=False,
                 boot_executed=False, launch_clearance=False)
    (HERE / 'full109-postauth-resume-control-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(value))


if __name__ == '__main__':
    main()
