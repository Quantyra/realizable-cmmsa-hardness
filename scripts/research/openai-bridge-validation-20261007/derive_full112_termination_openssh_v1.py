"""Bind an OpenSSH quiescence observation to unchanged dedicated termination gates."""
import ast,json
from pathlib import Path
from custody_checks import digest
HERE=Path(__file__).resolve().parent
def main():
    parent=HERE/'terminate_full112_builder02_after_custody.py'
    text=parent.read_text(encoding='utf-8')
    changes=[
        ("from finalize_builder02_bootstrap import SDK, FLAGS","from finalize_builder02_bootstrap import SDK, FLAGS\nfrom full112_dedicated_openssh_v2 import Session"),
        ("        out=cloud(['compute','ssh',VM,'--tunnel-through-iap','--command=ps -eo pid=,comm='])","        with Session(folder/'openssh-transport') as session:\n            out=session.ssh('ps -eo pid=,comm=').read_bytes()"),
    ]
    for old,new in changes:
        assert text.count(old)==1;text=text.replace(old,new)
    ast.parse(text)
    target=HERE/'terminate_full112_after_custody_openssh_v1.py';target.open('x',encoding='utf-8',newline='\n').write(text)
    wrapper=HERE/'run_full112_resume_step_v7.py';updated=wrapper.read_text(encoding='utf-8')
    anchor="'preserve_full111_complete_recovery_plans_v5.py'}"
    assert updated.count(anchor)==1
    updated=updated.replace(anchor,"'preserve_full111_complete_recovery_plans_v5.py', 'preserve_full111_complete_recovery_v4.py', 'terminate_full112_after_custody_openssh_v1.py'}")
    ast.parse(updated)
    next_wrapper=HERE/'run_full112_resume_step_v8.py';next_wrapper.open('x',encoding='utf-8',newline='\n').write(updated)
    record=dict(parent=parent.name,parent_sha256=digest(parent),target=target.name,target_sha256=digest(target),
        exact_replacements=[dict(old=a,new=b) for a,b in changes],
        original_custody_resource_native_terminal_quiescence_and_independent_termination_gates_retained=True,
        only_quiescence_transport_changed=True,SDK_describe_and_stop_unchanged=True,
        wrapper_parent_sha256=digest(wrapper),wrapper_sha256=digest(next_wrapper),
        cloud_action_performed=False,compiler_invoked=False)
    (HERE/'full112-termination-openssh-derivation-v1.json').open('x').write(json.dumps(record,indent=2)+'\n')
    print(json.dumps(dict(termination=target.name,wrapper=next_wrapper.name)),flush=True)
if __name__=='__main__':main()

