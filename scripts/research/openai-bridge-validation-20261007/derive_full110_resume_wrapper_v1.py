"""Derive only the complete-output wrapper for the frozen Full110 controls."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / 'run_full109_resume_step_v4.py'
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest().upper() == '76667AA95A905126DAB5D84A508777ADC5AE16EF21F2BAFC5570DCF5BA83B3B6'
    before = raw.decode('utf-8')
    tree = ast.parse(before)
    node = next(n for n in tree.body if isinstance(n, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == 'ALLOWED' for t in n.targets))
    lines = before.splitlines(keepends=True)
    old_allowed = ''.join(lines[node.lineno-1:node.end_lineno])
    new_allowed = "ALLOWED = {'stage_full110_builder02.py', 'full110_builder02_controller.py', 'full110_postprocess.py'}\n"
    replacements = [(old_allowed, new_allowed),
                    ('from full109_builder02_controller import ROOT', 'from full110_builder02_controller import ROOT'),
                    ("'research-resume-20261010'", "'research-resume-20261011'")]
    after = before
    for old, new in replacements:
        assert after.count(old) == 1
        after = after.replace(old, new)
    ast.parse(after)
    output = HERE / 'run_full110_resume_step_v1.py'
    output.open('xb').write(after.encode('utf-8'))
    value = dict(source=str(source), source_sha256=hashlib.sha256(raw).hexdigest().upper(),
                 output=str(output), output_sha256=hashlib.sha256(output.read_bytes()).hexdigest().upper(),
                 replacements=[dict(old=old, new=new) for old, new in replacements],
                 complete_stdout_stderr_and_terminal_retained=True,
                 compiler_controls_changed=False, frozen_capture_changed=False,
                 compiler_invoked=False, launch_clearance=False)
    (HERE / 'full110-resume-wrapper-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(value, indent=2)+'\n')
    print(json.dumps(value))


if __name__ == '__main__':
    main()
