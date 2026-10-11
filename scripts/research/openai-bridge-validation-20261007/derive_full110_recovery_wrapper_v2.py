"""Extend the complete-output wrapper only to the bounded cache lifecycle controller."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'run_full110_resume_step_v1.py'
assert digest(source) == 'AE67D5179EB39A557409369613C92598F405B82980FCF481ACE7D5259C71339D'
text = source.read_text(encoding='utf-8')
old = "ALLOWED = {'stage_full110_builder02.py', 'full110_builder02_controller.py', 'full110_postprocess.py'}"
new = "ALLOWED = {'run_full110_settled_cache_recovery_v1.py'}"
assert text.count(old) == 1
text = text.replace(old, new)
ast.parse(text)
target = HERE / 'run_full110_resume_step_v2.py'
target.open('xb').write(text.encode('utf-8'))
(HERE / 'full110-recovery-wrapper-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=source.name, source_sha256=digest(source), target=target.name, target_sha256=digest(target),
    exact_replacement=dict(old=old, new=new), original_wrapper_preserved=True), indent=2)+'\n')
print(json.dumps(dict(target=target.name, sha256=digest(target))))
