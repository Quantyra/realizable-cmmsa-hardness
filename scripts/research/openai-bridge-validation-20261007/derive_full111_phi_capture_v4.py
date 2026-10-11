"""Capture the separately offered one-line Fintype-shadow repair; retain v1 bytes."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'capture_full111_repair_offers_v3.py'
assert digest(source) == 'DA5B0C2EE649AFBF2B42ED2CF5E53C13A0F707E92ECF1DFFD4ED24088F94D8BB'
old_offer = HERE / 'full111-phi-repair-capture-v1/ExactPhiEigenrelation-v4.lean'
new_offer = HERE / 'full111-phi-repair-v2/ExactPhiEigenrelation-v4.lean'
old = old_offer.read_bytes()
line = b'  haveI : Fintype S := Fintype.ofFinite S\n'
assert old.count(line) == 1 and new_offer.read_bytes() == old.replace(line, b'')
text = source.read_text(encoding='utf-8')
changes = [('full111-phi-repair-v1', 'full111-phi-repair-v2'),
           ("'-repair-capture-v1'", "'-repair-capture-v2'")]
for before, after in changes:
    assert text.count(before) == 1
    text = text.replace(before, after)
ast.parse(text)
target = HERE / 'capture_full111_repair_offers_v4.py'
target.open('xb').write(text.encode('utf-8'))
(HERE / 'full111-phi-capture-control-derivation-v4.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=source.name, source_sha256=digest(source), target=target.name, target_sha256=digest(target),
    exact_replacements=changes, exact_single_line_deletion_verified=True,
    old_offer_sha256=digest(old_offer), new_offer_sha256=digest(new_offer), prior_offers_preserved=True), indent=2)+'\n')
print(json.dumps(dict(target=target.name, sha256=digest(target))))
