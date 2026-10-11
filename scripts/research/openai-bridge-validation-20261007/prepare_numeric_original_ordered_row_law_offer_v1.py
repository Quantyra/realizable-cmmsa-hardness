from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-original-ordered-row-law-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualTaggedOrderedQuestionSourceBridge', 'ActualTaggedQuestionRetainedMass',
                 'ActualTaggedQuestionMass', 'ActualQuestionMassBridge', 'ActualFiniteLaw',
                 'ActualTaggedConcreteStarLaw', 'ActualTaggedFixedCenterGeometry']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean/lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'

source = (OUT / 'ActualOriginalOrderedRowLaw.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['∑', '≤', '∀', 'ℚ'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['iidOrderedMass_eq_product', 'iidOrderedMass_normalized',
    'eligibleScore_of_good', 'orderedGood_score_mean',
    'iid_eligible_score_eq_goodMass_mul_mean', 'iid_score_lower_of_eligible_domination',
    'padded_iid_score_lower']
assert definitions == ['iidOrderedMass', 'eligibleScore']
checks = 'import PvNP.RealizableHardness.ActualOriginalOrderedRowLaw\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualOriginalOrderedRowLaw.' + name + '\n'
                  for name in definitions + exports)
argument = '''# Original ordered-row law

E002/S3137. Implements the complete 2026-10-11 Returning to the original ordered-row law argument recorded before translation in the numeric obligations note. Uncompiled and unaccepted.

The original row-tuple mass is exactly the product of uniform tagged-row weights, without conditioning on eligibility. Zero-extend any score on actual good U to all ordered tuples. The existing exact ordered-good pushforward identifies its conditional mean with the uniform-good-U mean. Summing over the eligible subtype then gives unconditional zero-extended mean equal to actualTaggedGoodMass times that good-U mean. Thus eligibility is paid explicitly in the original law. This includes zero scores and requires no independence assumption about the conditional score's later randomness.

A pointwise dominating total score has at least the same original-law mean. At the existing padding, the actual good mass is at least three quarters, so a nonnegative good-U mean bound B gives at least 3B/4. The explicitly displayed Nonempty good-U instance in the padded statement is already supplied by taggedGoodU_nonempty_of_padding under the same T>=4 and m>0 assumptions. It is not a new probabilistic premise.

This realizes only the first-question averaging step. The complete strategy must instantiate the score and its pointwise domination, preserve the deletion and advised-vector laws, provide the maximal-list selection and bind actual assignment acceptance. No arbitrary score in this source is claimed to be an already constructed strategy, and no source-NO or hardness conclusion follows alone. No new sampler or hardness premise is introduced. Parent pins are the exact failed/unaccepted Full114 input interfaces; this is not an accepted operator rebinding. No Lean or Lake ran locally.

Remaining to-do list: kernel/axiom/warning verification, actual strategy and outer-law instantiation, maximal-list/source NO, effective base/runtime, replay and independent/final certification gates.
'''
for name, data in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(data, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=[],
    toolchain=dict(value=toolchain.decode('utf-8').strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports,
    checked_definitions=definitions)))
