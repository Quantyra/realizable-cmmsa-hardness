from pathlib import Path
import hashlib
import json
import re

S = Path(__file__).resolve().parent
OLD = S / 'numeric-restricted-visible-pair-offer-20261011-v1'
OUT = S / 'numeric-restricted-visible-pair-offer-20261011-v2'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not OUT.exists()
original = (OLD / 'ActualRestrictedVisiblePair.lean').read_bytes()
assert sha(original) == 'A6C705BEA48F38EFE901A2CE35346EA573288E2F705F8AAEEA7C4482735C81C5'
before = b'  have hW := P.W.finrank_le\n  have hV := actualRetained_finrank I copies U s\n'
after = b'  have hW := P.W.finrank_le\n  have hE : Module.finrank (ZMod 2) (E I copies U) = 3 * J := by\n    simpa [TripleRestrictionRank.Vector, TripleRestrictionRank.Coord,\n      Module.finrank_pi, Nat.mul_comm] using (actualRowCoordinateEquiv I copies U).finrank_eq\n  have hV := actualRetained_finrank I copies U s\n'
assert original.count(before) == 1
repaired = original.replace(before, after)
assert repaired.replace(after, before) == original
code = repaired.decode('utf-8')
assert not repaired.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
OUT.mkdir()
(OUT / 'ActualRestrictedVisiblePair.lean').write_bytes(repaired)
for name in ['Checks.lean', '.gitattributes']:
    (OUT / name).write_bytes((OLD / name).read_bytes())
argument = (OLD / 'ARGUMENT.md').read_text(encoding='utf-8')
argument += '\nV2 is a single proof-side repair: add the explicit ambient finrank identity from the actual row-coordinate linear equivalence before the natural-number dimension arithmetic. Public declarations, their statements, imports, options and Checks are unchanged. Removing the added identity reverses exactly to captured V1. Neither source is compiled or accepted.\n'
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
manifest = json.loads((OLD / 'manifest.json').read_text(encoding='utf-8'))
manifest['schema'] = OUT.name
manifest['parent_capture'] = dict(index_sha256='B176CE9E62E2784B62F987D48FBBAE3EDDA3DD833A91DA4767218DDBCA86C403',
    source_sha256=sha(original), manifest_sha256=sha((OLD / 'manifest.json').read_bytes()))
manifest['repair'] = 'Explicit actual ambient finrank identity before restricted-window omega; exact reverse reconstruction verified.'
manifest['files'] = [dict(path=p.name, bytes=len(p.read_bytes()), sha256=sha(p.read_bytes())) for p in sorted(OUT.iterdir())]
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(repaired), checks_sha256=sha((OUT / 'Checks.lean').read_bytes()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exact_reverse=True)))
