"""Add only the explicit OpenSSH recovery continuation to the retained wrapper."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent


def main():
    source = HERE/'run_full112_resume_step_v2.py'
    before = "'inspect_full111_recovery_state_v1.py'}"
    after = "'inspect_full111_recovery_state_v1.py', 'run_full111_settled_cache_openssh_v2.py'}"
    text = source.read_text(encoding='utf-8'); assert text.count(before) == 1
    text = text.replace(before, after); ast.parse(text)
    target = HERE/'run_full112_resume_step_v3.py'; target.open('xb').write(text.encode('utf-8'))
    (HERE/'full112-openssh-wrapper-derivation-v3.json').open('x').write(json.dumps(dict(
        parent=str(source),parent_sha256=digest(source),target=str(target),sha256=digest(target),
        replacement=[before,after],compiler_invoked=False),indent=2)+'\n')


if __name__ == '__main__': main()
