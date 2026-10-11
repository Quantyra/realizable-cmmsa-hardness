"""Allow only named seven-scope custody/audit and unchanged-scope native continuations."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/'run_full112_resume_step_v4.py';text=source.read_text(encoding='utf-8')
    old="'derive_full111_settled_cache_recovery_v2.py'}"
    new="'derive_full111_settled_cache_recovery_v2.py', 'preserve_full111_seven_recovery_plans_v3.py', 'audit_full111_settled_cache_recovery_v2.py', 'stage_full112_after_recovery_openssh_v2.py', 'run_full112_native_openssh_v1.py'}"
    assert text.count(old)==1;text=text.replace(old,new);ast.parse(text)
    target=HERE/'run_full112_resume_step_v5.py';target.open('xb').write(text.encode())
    (HERE/'full112-openssh-wrapper-derivation-v5.json').open('x').write(json.dumps(dict(
        parent=source.name,parent_sha256=digest(source),target=target.name,sha256=digest(target),replacement=[old,new],
        compiler_invoked=False,cloud_action=False),indent=2)+'\n')


if __name__=='__main__':main()
