"""Correct the observed archive member name; preserve the failed control."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    parent = HERE / 'capture_full111_diagnostics_v1.py'
    text = parent.read_text(encoding='utf-8')
    replacements = [
        ('full111-native-diagnostic-packet-v1', 'full111-native-diagnostic-packet-v2'),
        ("'terminal.json'", "'dedicated-worker-terminal.json'")]
    for old, new in replacements:
        assert text.count(old) == 1
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / 'capture_full111_diagnostics_v2.py'
    target.open('xb').write(text.encode('utf-8'))
    failure = HERE / 'full111-native-diagnostic-packet-v1'
    result = dict(schema='full111-diagnostic-capture-derivation-v2',
        parent_sha256=digest(parent), target_sha256=digest(target), exact_replacements=replacements,
        root_tool_observation=dict(original_capture_native_exit=1,
            exception="KeyError: filename 'terminal.json' not found",
            partial_original_files=[dict(path=p.name, bytes=p.stat().st_size, sha256=digest(p)) for p in sorted(failure.iterdir())],
            direct_tool_traceback_observed=True, direct_tool_traceback_archived=False,
            later_inline_derivation_exit=1, inline_derivation_error='PowerShell quoting produced an unterminated Python string; no file written',
            absent_successor_invocation_exit=1, absent_successor_error='ModuleNotFoundError; no compiler or cloud operation'),
        failed_control_and_partial_output_preserved=True, compiler_invoked=False)
    (HERE / 'full111-diagnostic-capture-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
