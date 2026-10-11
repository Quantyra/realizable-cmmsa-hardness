from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-visible-joint-success-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ZoomOutJoint', 'GoodAdvice', 'AdviceExceptions', 'GrassmannIncidence']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
relative = 'numeric-visible-posterior-ledger-offer-20261011-v1/ActualVisiblePosteriorLedger.lean'
raw = (S / relative).read_bytes()
expected = 'B971663A0C2FC5BA32079BE555BF5D45003D78A687D7156B97DAFFE2CA0149B5'
assert sha(raw) == expected
candidates = [dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False)]
source = (OUT / 'ActualVisibleJointSuccess.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['∑', '≤', '→', 'ℚ', '↔'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['goodFavorable_eq_true', 'favorable_marginal_lower',
    'jointVisibleSuccess_disintegration', 'ready_visible_joint_success']
assert definitions == ['goodFavorable', 'visibleEvent', 'jointVisibleSuccess']
checks = 'import PvNP.RealizableHardness.ActualVisibleJointSuccess\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisibleJointSuccess.' + name + '\n'
                  for name in definitions + exports)
argument = '''# Same actual joint law for visible success

E002/S3137. Implements the recorded 2026-10-11 Same-joint-law integration of the visible score argument. Uncompiled and unaccepted.

Remove both actual bad-advice events from the favorable event under uniform ambient advice, subtracting at most their masses. One actual adviceTV charge transfers the result to the actual marginal. Expand the draw-first joint success event, interchange the two finite sums and apply bayes_joint on favorable advice. GoodAdvice proves these marginals positive; all other terms vanish by the event indicator. The actual visible posterior C/4 theorem then supplies the conditional factor, yielding the marginal lower bound times C/4 in the same joint experiment.

This theorem keeps the favorable predicate and its original fixed-score decoder, along with the geometric visible-score comparison, explicit until the actual named-advice and row-frame sources instantiate them. It does not assert that an arbitrary favorable event or arbitrary score is a legitimate decoder. No reciprocal posterior-density loss, independent event, unconditional draw success or final source NO is claimed.

Route assessment after the ledger, scalar margin and joint-law increments: these give the required probability composition on actual laws but are insufficient without actual score identities and the named-advice witness instantiation. Those applications are in active translation. All-window maximal-list selection, legitimate prover-two input dependence, random extensions and the actual outer source-game law remain necessary. Retain this route while making those missing implications explicit; helper counts do not constitute acceptance. Direct parent interfaces match failed/unaccepted Full114; the ledger dependency has an immutable pin. No local Lean or Lake ran.

Remaining to-do list: kernel/axiom/warning verification, actual named-advice/row-frame instantiation, maximal-list/strategy/source NO, effective base/runtime, replay and independent/final certification.
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
    dependencies=deps, candidate_dependencies=candidates,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports,
    checked_definitions=definitions)))
