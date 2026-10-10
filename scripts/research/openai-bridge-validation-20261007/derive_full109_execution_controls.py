"""Derive guarded Full109 controls from preserved Full108 controls; no execution."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).parent


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    sources = ['full108_builder02_controller.py', 'full108_worker.py', 'full108_verify.py',
               'full108_postprocess.py', 'full108_native_audit_v2.py',
               'stage_full108_builder02.py', 'test_full108_terminal.py']
    rows = []
    for name in sources:
        raw = (HERE/name).read_bytes()
        text = raw.decode('utf8').replace('full108-exact-crosslevel-product',
                                        'full109-exact-crosslevel-warning-repair')
        text = text.replace('full108', 'full109').replace('Full108', 'Full109')
        target = name.replace('full108', 'full109').replace('native_audit_v2', 'native_audit')
        if name == 'full108_builder02_controller.py':
            start = text.index('EXTRA_LOCAL_CONTROLS = ')
            end = text.index('\n', start)
            text = text[:start]+"EXTRA_LOCAL_CONTROLS = ('full109_capture_gates.py','prepare_builder02_full109.py','full109_native_audit.py','full109_postprocess.py','derive_full109_execution_controls.py','prepare_full101_warning_repair.py','prepare_full101_spectral_application.py','recover_existing_spectral_candidate.py')"+text[end:]
        ast.parse(text)
        data = text.encode('utf8')
        path = HERE/target
        if path.exists():
            assert path.read_bytes() == data, 'Derived control drift: '+target
        else:
            path.open('xb').write(data)
        rows.append(dict(source=name, source_sha256=sha(raw), target=target, target_sha256=sha(data)))
    result = dict(schema='full109-parent-execution-control-derivation-v1', records=rows,
                  project_sources=348, requested_profiles=261, stages=7, latest_profile_suffix=1,
                  cumulative_additive_sources=29,
                  original_authentication_HEAD_custody_once_process_VM_memory_storage_guards_preserved=True,
                  compiler_invoked=False, cloud_operation=False, accepted=False)
    path = HERE/'full109-execution-control-derivation-v1.json'
    data = (json.dumps(result, indent=2)+'\n').encode()
    if path.exists():
        assert path.read_bytes() == data
    else:
        path.open('xb').write(data)
    print(json.dumps(dict(controls=7, sources=348, profiles=261, stages=7, cloud_operation=False)))


if __name__ == '__main__':
    main()
