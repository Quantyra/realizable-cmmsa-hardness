from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-hside-visible-table-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualTaggedSelectedDecoderBridge', 'ActualStarSpanIntersection',
                 'ActualTaggedFixedCenterGeometry', 'ActualTaggedPresentedSelection']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for relative, expected in [
    ('numeric-hside-full-zoom-offer-20261011-v2/ActualHSideFullZoom.lean',
     'A7AB365CCC35C6B9D72879DFBE095E41D2DBEDFAAB1E1B45FBC3FB5D46089E6D'),
    ('numeric-visible-completion-offer-20261011-v1/ActualVisibleQuestionCompletion.lean',
     '84D7E6F45BAC5519520ED1AED6FBE57D724F08B6F5BC80893BB5582D612C80B0')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidate_deps.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualHSideVisibleTable.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['visible_table_eq_actual_full_zoom_table']
checks = 'import PvNP.RealizableHardness.ActualHSideVisibleTable\n\n'
checks += '#print axioms PvNP.RealizableHardness.ActualHSideVisibleTable.visible_table_eq_actual_full_zoom_table\n'
argument = '''# Actual full-zoom and visible-input table identity

E002/S3137. Complete argument was recorded before translation in the existing numeric obligations note after Selected H-side leaf charge and route assessment. This source is uncompiled and unaccepted.

For an internal 2h-dimensional leaf L of an original good question U, its actual coordinate inclusion maps it into global tagged-variable coordinates. Assume that image lies in visible space X and is transverse to both the original equation span and the fixed completion selected only from X. The captured visibleLeafTable_agrees_with_original then identifies the visible entry with the original globally selected canonical label on image(L)+H_U. The internal full-zoom table evaluates the same global table on image(H+L). Every row equation is supported in U, so the equation-span comap followed by the coordinate inclusion equals H_U. Map distributes over the subspace sum, identifying these domains. The actual included leaf vector is identical on both sides, proving pointwise entry equality.

This supplies the exact same-table identity needed after the original-law/H-side agreement transport. The second-prover table still uses only X and globally fixed choices. Both transversality hypotheses remain visible; no equality on exceptional leaves, independent completion law, posterior bound or complete strategy is asserted. The original-H and completion-dependent exceptional probabilities must still be paid in the joint proof. Four parent interfaces match failed/unaccepted Full114 and both candidate dependencies have exact frozen pins. One public theorem has an axiom request. No local Lean or Lake ran.

Remaining to-do list: authoritative kernel/axiom/warning verification, actual posterior/exception integration, legitimate decoder/source NO, runtime, replay and all mandatory independent/final certification gates.
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
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
