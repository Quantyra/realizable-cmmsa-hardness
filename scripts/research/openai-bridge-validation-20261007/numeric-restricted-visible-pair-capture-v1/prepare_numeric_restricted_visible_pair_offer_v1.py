from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-restricted-visible-pair-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'TripleRestrictionDimension',
                 'TripleRestrictionRank', 'ActualStarSpanIntersection']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for relative, expected in [
    ('numeric-actual-visible-leaf-loss-offer-20261011-v1/ActualVisibleLeafAgreementLoss.lean',
     '87085914701B98902AE97DA9DBE09D26BCF2DAE9762F2C5C2CDFB7824343BF0D'),
    ('numeric-row-deletion-offer-20261011-v1/ActualTaggedRowDeletion.lean',
     'F844D422FEF025399462872F9F59D6EC1E8BA41C28DCE4D95B20C463B876390B')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidate_deps.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualRestrictedVisiblePair.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['⊓', '≤', '⟨', '⟩'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['restrictedPair_apply', 'actualRetained_finrank',
                   'restrictedPair_finrank_lower', 'actual_restricted_visible_agreement_lower']
assert definitions == ['restrictedPair']
checks = 'import PvNP.RealizableHardness.ActualRestrictedVisiblePair\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualRestrictedVisiblePair.' + n + '\n'
                  for n in definitions + exports)
argument = '''# Restricting the original pair to the actual visible window

E002/S3137. Implements the window and label step of the already recorded 2026-10-11 Two-table leaf loss and the posterior margin argument. Uncompiled and unaccepted.

Given the actual original decoded pair P and a deletion draw containing Q, construct P' with window P.W intersect actualRetained and label P.g restricted by the actual inclusion. Its functional values are exactly the original values. The captured actual row-coordinate map equality and dimension-preserving linear equivalence identify actualRetained dimension with 3J minus twice the original draw's drop count.

The finite subspace dimension-addition formula and dim(W+V)<=dim(E) imply dim(W intersect V)>=dim(V)-codim(W). Thus original codimension at most r and drop count at most T imply dim(P'.W)>=3J-2T-r. No rank-stability premise is needed for this lower bound; rank stability remains necessary for the later random-extension calculation.

Under the explicit scalar slack J+2h+1<=3J-2T-r and advice/query guards, all interval-transversality guards hold for P'. The captured actual visible-table comparison then applies, and monotonicity of the reciprocal power bounds its error by 2/2^(2J-2T-2h-r-1). Both original and completion advice-transversality premises are retained, and their exclusions must still be charged under the posterior. No existence of a favorable draw or changed draw law is asserted. The complete posterior integration and selected numeric substitution remain open. Four parent interfaces match failed/unaccepted Full114 and two candidate dependencies have exact pins. No local Lean or Lake ran.

Remaining to-do list: authoritative kernel/axiom/warning verification, row-coordinate posterior score transport and numeric margins, legitimate decoder/source NO, common base/runtime, replay and all mandatory independent/final certification gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    data = path.read_bytes()
    assert not data.startswith(b'\xef\xbb\xbf') and '\ufffd' not in data.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(data), sha256=sha(data)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports,
    checked_definitions=definitions)))
