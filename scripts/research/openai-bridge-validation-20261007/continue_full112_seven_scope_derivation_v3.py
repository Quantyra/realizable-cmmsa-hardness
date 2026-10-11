"""Finish local derivation after a string-boundary error; preserve all v2 bytes."""
import ast
import json
from pathlib import Path
from custody_checks import digest
from derive_full112_seven_scope_recovery_v2 import derive, ROWS, HERE


def main():
    prior=HERE/'derive_full112_seven_scope_recovery_v2.py'
    text=prior.read_text(encoding='utf-8')
    start=text.index('    wrapper=NEXT/')
    stop=text.index('    parent=(HERE/',start)
    target=HERE/'full111-recovery-eight-gib-plan-failure-v1'
    evidence=json.loads((target/'index.json').read_bytes())
    for row in evidence['files']:assert digest(target/row['copy'])==row['sha256']
    helper=HERE/'derive_full111_settled_cache_recovery_v2.py'
    ast.parse(helper.read_text(encoding='utf-8'))
    replacement="    target=HERE/'full111-recovery-eight-gib-plan-failure-v1'\n    rows=json.loads((target/'index.json').read_bytes())['files']\n    for row in rows: assert digest(target/row['copy'])==row['sha256']\n    ROWS.append(dict(already_derived='derive_full111_settled_cache_recovery_v2.py',sha256="+repr(digest(helper))+", original_derivation='derive_full112_seven_scope_recovery_v2.py', original_derivation_sha256="+repr(digest(prior))+"))\n"
    text=text[:start]+replacement+text[stop:]
    old="end=parent.index('            preamble +=',start)"
    new="end=parent.index('\\n            preamble +=',start)+1"
    assert text.count(old)==1;text=text.replace(old,new)
    text=text.replace('full112-seven-scope-recovery-derivation-v2.json','full112-seven-scope-recovery-derivation-v3.json')
    ast.parse(text)
    successor=HERE/'derive_full112_seven_scope_recovery_v3.py';successor.open('xb').write(text.encode())
    (HERE/'full112-seven-scope-local-derivation-failure-v2.json').open('x').write(json.dumps(dict(
        original_control=str(prior),original_control_sha256=digest(prior),original_tool_chunk='4fe973',native_exit=1,
        diagnostic='ValueError: substring not found',raw_tool_stream_archive_claimed=False,
        completed_outputs=[str(target),str(helper)],compiler_invoked=False,cloud_action=False,
        continuation=str(successor),continuation_sha256=digest(successor),
        repair='Use newline-anchored exact indentation boundary; preserve completed output instead of rerunning it.'),indent=2)+'\n')
    import importlib.util
    spec=importlib.util.spec_from_file_location('local_continuation',successor)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.main()


if __name__=='__main__':main()
