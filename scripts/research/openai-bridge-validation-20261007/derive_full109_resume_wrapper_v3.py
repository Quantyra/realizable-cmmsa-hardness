"""Preserve v2 and add collision-free log directories and review-only steps."""
import ast
import json
from pathlib import Path
from custody_checks import digest

here = Path(__file__).parent
source = here/'run_full109_resume_step_v2.py'
text = source.read_text(encoding='utf-8')
replacements = [
    ('import sys\n', 'import sys\nimport uuid\n'),
    ("    'audit_full109_pending_trace_plans_v2.py',", "    'audit_full109_pending_trace_plans_v2.py',\n    'prepare_full109_consumption_review_sources.py',\n    'audit_full109_prior_review_reuse_v1.py',\n    'prepare_full109_material_integration_v1.py',\n    'run_full109_material_integration_v1.py',"),
    ("datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')", "(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')+'-'+uuid.uuid4().hex[:12])"),
    ("    (folder / source.name).write_bytes(source.read_bytes())", "    (folder / source.name).write_bytes(source.read_bytes())\n    (folder / 'wrapper.snapshot.py').write_bytes(Path(__file__).read_bytes())"),
]
for old, new in replacements:
    assert text.count(old) == 1
    text = text.replace(old, new)
ast.parse(text)
target = here/'run_full109_resume_step_v3.py'
target.open('x', encoding='utf-8', newline='\n').write(text)
record = dict(parent_sha256=digest(source), successor_sha256=digest(target), replacements=replacements,
              native_output_capture_and_terminal_handling_unchanged=True, compiled_inputs_changed=False)
(here/'full109-resume-wrapper-derivation-v3.json').open('x', encoding='utf-8', newline='\n').write(json.dumps(record, indent=2)+'\n')
print(json.dumps(dict(successor=str(target), sha256=digest(target))))
