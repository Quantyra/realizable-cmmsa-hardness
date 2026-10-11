from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S/'numeric-completion-pullback-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S/'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualOccurrenceAllocation', 'ActualStarQuestionSupport', 'ActualStarSpanIntersection',
                 'ActualTaggedFixedCenterGeometry', 'ActualTaggedConcreteStarLaw',
                 'ActualRhsFunctionalConstruction', 'TripleRestrictionRank']:
        member = 'lean/PvNP/RealizableHardness/'+name+'.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF/member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for folder, file, pin in [
    ('numeric-row-deletion-offer-20261011-v1', 'ActualTaggedRowDeletion.lean', 'F844D422FEF025399462872F9F59D6EC1E8BA41C28DCE4D95B20C463B876390B'),
    ('numeric-visible-completion-offer-20261011-v1', 'ActualVisibleQuestionCompletion.lean', '84D7E6F45BAC5519520ED1AED6FBE57D724F08B6F5BC80893BB5582D612C80B0')]:
    path = S/folder/file
    raw = path.read_bytes()
    assert sha(raw) == pin
    candidate_deps.append(dict(path=str(path), module=path.stem, bytes=len(raw), sha256=pin, status='uncompiled'))
source = (OUT/'ActualCompletionEquationPullback.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 8, exports
assert len(definitions) == 5, definitions
checks = 'import PvNP.RealizableHardness.ActualCompletionEquationPullback\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualCompletionEquationPullback.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualCompletionEquationPullback.'+n+'\n' for n in exports)
argument = '''# Actual completion equation-span pullback

E002/S3137. Complete argument was recorded before translation in the planning numeric obligations note, section 2026-10-11 Visible table and extension captures; varying-completion exception argument. This is uncompiled.

The inverse actual row-coordinate equivalence followed by the original coordinate-space inclusion defines an injective linear map from Vector J to the actual global tagged-variable ambient. The visible set for draw d is the actual retainedVariables set of the inverse row draw. completionForDraw invokes the already fixed completion on that visible set alone; equal visible sets give the same completion. There is no extra original-U input to the second-prover strategy. U indexes only the proof frame for the conditional law.

Pull back the completion's actual equation span along that injection. Good-question row independence and the completion cardinality prove its global equation span has dimension J. Restriction of the injection maps the pullback injectively into that span, so its dimension is at most J. This discharges the dimension hypothesis of the separate varying-subspace probability theorem for the actual chosen completion, with no independent choice or uniform-completion assumption.

Composition of the exact retained row-coordinate equality with the global visible-space equality proves the image of retained(d) is precisely the visibleCoordinateSpace of the same visible set. Consequently any retained advice maps into that space. For any coordinate subspace Q, its intersection with the pulled-back completion span is zero exactly when its global image has zero intersection with the actual completion span. In one direction choose a preimage of every vector in the global intersection; in the other direction injectivity shows a zero global image has zero preimage. Negating gives exact equivalence of the two exceptional events, pointwise for every draw and every Q.

The separate arbitrary draw-dependent subspace estimate can therefore be instantiated with this actual pullback without supplying a new dimension premise. The event equivalence also permits exact rewriting of the same original joint/posterior sums. This source deliberately has no probability-bound premise or conclusion; the actual count, original-law average, Markov/TV and selected numerical substitutions are subsequent integration obligations. Leaf-level double-transversality charges and the full legitimate decoder remain open.

Seven project sources match Full114 archive members; actual row and visible-completion candidate sources are exact-byte pinned. Eight theorem axiom requests and five definition checks are included. No local Lean/Lake ran. Full114 remains unaccepted and GCP verification must rebind the complete closure to the accepted operator parent.

Remaining to-do list: GCP kernel/axiom/warning verification, exact probability-theorem specialization, selected numeric charges, decoder/source NO and all retained runtime/review gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT/name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False, compiler_invoked=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN), dependencies=deps, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
