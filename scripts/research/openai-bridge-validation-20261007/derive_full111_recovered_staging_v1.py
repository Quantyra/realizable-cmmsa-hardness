"""Fresh Full111 staging on the independently audited existing recovery lifecycle."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'stage_full111_builder02.py'
original = source.read_text(encoding='utf-8')
start = original.index("    if before['status'] != ('RUNNING' if resume else 'TERMINATED'):")
end = original.index('    after = describe()', start)
removed = original[start:end]
replacement = '''    if before['status'] != 'RUNNING':
        raise RuntimeError('Audited recovery VM is not RUNNING; preserve state')
    if (ROOT/'launch-once.json').exists():
        raise RuntimeError('Full111 attempt already exists; retain original handle')
    recovery = validate_local_audit()
    if str(recovery['state']['id']) != VM_ID:
        raise RuntimeError('Recovery lifecycle identity mismatch')
    recovery_path = AUDIT / 'audit.json'
    (folder/'recovery-admission.json').open('x', encoding='utf-8').write(json.dumps(dict(
        audit=str(recovery_path), sha256=digest(recovery_path), existing_owned_lifecycle=True,
        VM_start_performed=False, all_seven_recovery_scopes_verified=True), indent=2)+'\\n')
    cloud(['compute','ssh',VM,'--tunnel-through-iap',
           '--command=set -e; test ! -e '+STAGE+'; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-prepared; test ! -e /home/dfredriksen_quantyra_org/'+ROOT.name+'-launch-once.json'])
'''
text = original[:start] + replacement + original[end:]
changes = [
    ('from custody_checks import digest', 'from custody_checks import digest\nfrom audit_full110_settled_cache_recovery_v1 import AUDIT, validate_local_audit'),
    ('def main(resume=False):', 'def main():'),
    ("    if sys.argv[1:] not in ([], ['--resume-staging']):\n        raise SystemExit('Default staging or --resume-staging required')\n    main(sys.argv[1:] == ['--resume-staging'])",
     "    if sys.argv[1:]:\n        raise SystemExit('Fresh staging on audited recovery lifecycle requires no arguments')\n    main()"),
    ('"""Authorized dedicated02 start/transport/preflight; no compiler invocation."""',
     '"""Fresh transport/preflight on audited recovery lifecycle; no start or compiler."""')]
for old, new in changes:
    assert text.count(old) == 1
    text = text.replace(old, new)
ast.parse(text)
target = HERE / 'stage_full111_after_recovery_v1.py'
target.open('xb').write(text.encode('utf-8'))
wrapper_source = HERE / 'run_full111_resume_step_v1.py'
wrapper = wrapper_source.read_text(encoding='utf-8')
old = "ALLOWED = {'stage_full111_builder02.py', 'full111_builder02_controller.py', 'full111_postprocess.py'}"
new = "ALLOWED = {'stage_full111_after_recovery_v1.py', 'audit_full110_settled_cache_recovery_v1.py'}"
assert wrapper.count(old) == 1
wrapper = wrapper.replace(old, new)
ast.parse(wrapper)
wrapper_target = HERE / 'run_full111_resume_step_v2.py'
wrapper_target.open('xb').write(wrapper.encode('utf-8'))
(HERE / 'full111-recovered-staging-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=source.name, source_sha256=digest(source), target=target.name, target_sha256=digest(target),
    removed_admission_block=removed, replacement_admission_block=replacement, exact_replacements=changes,
    wrapper_source=wrapper_source.name, wrapper_source_sha256=digest(wrapper_source),
    wrapper_target=wrapper_target.name, wrapper_target_sha256=digest(wrapper_target),
    wrapper_exact_replacement=[old, new], unchanged_resource_and_native_preflight=True,
    fresh_remote_stage_prepared_and_launch_absence_required=True, VM_start_or_compiler_invoked=False), indent=2)+'\n')
print(json.dumps(dict(controls_derived=2, stage_executed=False, compiler_invoked=False)))
