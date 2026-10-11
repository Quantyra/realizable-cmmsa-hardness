"""Preserve the executed rectangular capture control; bind Phi's offered filenames."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'capture_full111_repair_offers_v1.py'
target = HERE / 'capture_full111_repair_offers_v2.py'
text = source.read_text(encoding='utf-8')
changes = [
    ("    folder_name, stem = SCOPES[scope]\n", "    assert scope == 'phi'\n    folder_name, stem = SCOPES[scope]\n"),
    ("(offer / (stem + '.lean'))", "(offer / (stem + '-v4.lean'))"),
    ("offer / (stem + 'Checks.lean')", "offer / (stem + 'Checks-v4.lean')"),
    ("digest(offer / (stem + '.lean'))", "digest(offer / (stem + '-v4.lean'))"),
]
records = []
for old, new in changes:
    count = text.count(old)
    assert count == 1, (old, count)
    text = text.replace(old, new)
    records.append(dict(old=old, new=new, occurrences=count))
ast.parse(text)
target.open('xb').write(text.encode('utf-8'))
(HERE / 'full111-phi-capture-control-derivation-v2.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=source.name, source_sha256=digest(source), target=target.name, target_sha256=digest(target),
    exact_replacements=records, executed_v1_control_preserved=True), indent=2)+'\n')
print(json.dumps(dict(target=target.name, sha256=digest(target))))
