from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-actual-visible-leaf-loss-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'ActualRhsFunctionalConstruction',
                 'ActualStarSpanIntersection', 'ActualTaggedConcreteStarLaw']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for relative, expected in [
    ('numeric-hside-visible-table-offer-20261011-v1/ActualHSideVisibleTable.lean',
     '2DFFBB7DD8461A185D91A6DCA1FB7B869C7D701F39BF49ED6B390D912366AEA8'),
    ('numeric-two-table-leaf-loss-offer-20261011-v1/ActualTwoTableLeafLoss.lean',
     '8FE6FA699BD78C52ED73E5BD138C2C28840EE4B18AE93FB1B3B9B93AB2B6DDEE'),
    ('numeric-completion-pullback-offer-20261011-v1/ActualCompletionEquationPullback.lean',
     '196E930D224879EB1F0FCD6D8B5B0D1A5CAA787742445D00A22673AD49277C43')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidate_deps.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualVisibleLeafAgreementLoss.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['⊓', '≤', '→', '↔'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['actual_side_dimensions_le', 'visible_entry_eq_original',
                   'visible_agreement_ge_original_sub_dyadic',
                   'actual_draw_visible_agreement_ge_original_sub_dyadic']
assert definitions == ['originalSideSpace', 'visibleSideSpace', 'visibleTableInOriginalCoordinates']
checks = 'import PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisibleLeafAgreementLoss.' + n + '\n'
                  for n in definitions + exports)
argument = '''# Actual visible-table leaf loss

E002/S3137. This implements the actual retained-table application in the recorded planning section 2026-10-11 Two-table leaf loss and the posterior margin. Uncompiled and unaccepted.

Represent the already defined global visible-only table on the original question's coordinate space by composing each leaf entry with the actual coordinate inclusion. Pull both original and completion equation spans back through that same inclusion. Their dimensions are at most J by injectivity and the actual good-question equation-rank theorem. An elementwise proof identifies zero intersection before and after the injection.

The captured actual visible-table entry theorem then supplies equality to the original full-zoom table on every doubly transverse visible leaf. The generic two-table theorem applies without an assumed table-equality premise: every leaf lies inside the same decoded window, whose global image is contained in the visible coordinate space. This gives the exact twice-dyadic agreement loss on the same advice, pair and full zoom. The actual row-deletion specialization derives visible support from actualRetained_map_visible and window containment in actualRetained, with no replacement draw or sampling law.

The original question is an input to the coordinate representation only; the global visibleLeafTable remains the fixed visible-only construction. This source does not prove a full second-prover strategy, the actual W-intersection restriction pair and dimension lower bound, the row-coordinate posterior transport, selected numerical error budget, maximal-list selection, or source NO. These are the remaining application obligations, not supplied favorable-event hypotheses. Four parent sources match failed/unaccepted Full114; three direct candidate inputs are pinned exactly. No Lean or Lake ran locally.

Remaining to-do list: authoritative kernel/axiom/warning verification, actual restricted-pair/dimension and posterior integration, legitimate decoder/source NO, common base/runtime, replay and all mandatory independent/final certification gates.
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
