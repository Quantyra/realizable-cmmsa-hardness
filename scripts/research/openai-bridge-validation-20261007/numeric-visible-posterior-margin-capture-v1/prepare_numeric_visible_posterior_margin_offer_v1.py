from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-visible-posterior-margin-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ZoomOutPosterior', 'GoodAdvice', 'SamplerParameters']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidates = []
for relative, expected in [
    ('numeric-varying-completion-exception-offer-20261011-v7/ActualSelectedCompletionPosteriorBound.lean',
     'BA0B71DD1230F84145F13C34D758C731C0E327502FBCCD400974BEDCDD6AE0CC'),
    ('numeric-robust-real-offer-20261011-v2/ActualNumericRobustReal.lean',
     '3437068369905FDF688E52453245D6EC6E6ECAB1337D741153A618F081650CD7')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidates.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualVisiblePosteriorMargin.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['≤', '∧', 'ℚ', 'ℝ'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['actual_leaf_exponent_and_window_slack', 'actual_visible_posterior_margin',
    'selected_visible_posterior_margin']
checks = 'import PvNP.RealizableHardness.ActualVisiblePosteriorMargin\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisiblePosteriorMargin.' + name + '\n'
                  for name in exports)
argument = '''# Selected visible posterior numerical margin

E002/S3137. Implements the scalar step of the recorded 2026-10-11 Posterior loss ledger and its numerical margin argument. Uncompiled and unaccepted.

The actual block lower bound J>=4*h^4, h>=16 and r<=h imply the retained-leaf exponent 2J-2*h^4-2h-r-1>=10*h^2 and the full required window slack J+2h+1<=3J-2*h^4-r. Therefore the per-side leaf cost epsilon is at most qdecay(10,h). Zeta is also at most that quantity, so the transfer error plus two leaf errors plus four exclusion charges is at most seven qdecay(10,h).

The inequality 10*h^2>=2h+7 and 2^7>=70 imply seven qdecay(10,h)<=2^(-2h)/10. The actual original threshold e>=2^(-2h) and the single rational C>e/5 yield a strict bound below C/2. The exported weak bound supplies exactly the margin expected by ActualVisiblePosteriorLedger. The selected specialization obtains the height/rank facts from the same existing numericSourceFloor and refresh_threshold_bounds; it introduces no extra draw-dependent choice or favorable mass assumption.

This source discharges scalar comparisons only. Readiness and the completion bad-advice bound use the separately captured common-base construction. The actual pointwise canonical-table and row-frame score identities, legitimate strategy, all-window list estimates and source NO remain application obligations. Parent interfaces are exact failed/unaccepted Full114 pins and both candidate dependencies are immutable. No local Lean or Lake ran.

Remaining to-do list: kernel/axiom/warning verification, actual score and posterior integration, complete strategy/source NO, effective base/runtime, replay and independent/final certification.
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
    public_axiom_requests=exports, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
