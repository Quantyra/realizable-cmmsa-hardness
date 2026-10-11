"""Bind both source filename occurrences; retain the failed v2 derivation unchanged."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'capture_full111_repair_offers_v1.py'
target = HERE / 'capture_full111_repair_offers_v3.py'
text = source.read_text(encoding='utf-8')
changes = [
    ("    folder_name, stem = SCOPES[scope]\n", "    assert scope == 'phi'\n    folder_name, stem = SCOPES[scope]\n", 1),
    ("(offer / (stem + '.lean'))", "(offer / (stem + '-v4.lean'))", 2),
    ("offer / (stem + 'Checks.lean')", "offer / (stem + 'Checks-v4.lean')", 1),
]
records = []
for old, new, count in changes:
    assert text.count(old) == count
    text = text.replace(old, new)
    records.append(dict(old=old, new=new, occurrences=count))
ast.parse(text)
assert not (HERE / 'capture_full111_repair_offers_v2.py').exists()
target.open('xb').write(text.encode('utf-8'))
(HERE / 'full111-phi-capture-control-derivation-v3.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=source.name, source_sha256=digest(source), target=target.name, target_sha256=digest(target),
    exact_replacements=records, executed_v1_control_preserved=True,
    v2_original_tool_chunk='b848d3', v2_native_exit=1, v2_failure='Expected one filename occurrence, found two',
    v2_target_created=False, v2_raw_stream_archive_claimed=False,
    v2_failed_control_sha256=digest(HERE / 'derive_full111_phi_capture_v2.py')), indent=2)+'\n')
print(json.dumps(dict(target=target.name, sha256=digest(target))))
