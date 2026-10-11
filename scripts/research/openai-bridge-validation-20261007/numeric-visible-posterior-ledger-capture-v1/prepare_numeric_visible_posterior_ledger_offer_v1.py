from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-visible-posterior-ledger-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ZoomOutJoint', 'ZoomOutTransfer', 'GoodAdvice', 'AdviceExceptions',
                 'GrassmannIncidence', 'PosteriorReweighting', 'PosteriorDensity']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
relative = 'numeric-varying-completion-exception-offer-20261011-v7/ActualVaryingCompletionException.lean'
raw = (S / relative).read_bytes()
expected = '5B6182E790DFEFD70B86D2AADD25EBF12BF5BE382D53A4A95F3939DBE4B24252'
assert sha(raw) == expected
candidates = [dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False)]
source = (OUT / 'ActualVisiblePosteriorLedger.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['∑', '≤', '→', 'ℚ'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['charged_mean_lower', 'visible_success_mass_lower',
    'conditional_zero_of_not_contained', 'excluded_mass_le', 'ready_visible_posterior_success']
assert definitions == ['chargedScore', 'excluded']
checks = 'import PvNP.RealizableHardness.ActualVisiblePosteriorLedger\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisiblePosteriorLedger.' + name + '\n'
                  for name in definitions + exports)
argument = '''# Actual posterior visible-score loss ledger

E002/S3137. Implements the finite averaging and actual posterior exclusion steps of the recorded 2026-10-11 Posterior loss ledger and its numerical margin argument. Uncompiled and unaccepted.

For a normalized finite law, zero the visible score on the excluded event. Its mean is at least the original mean minus the pointwise comparison loss minus the actual excluded mass. The existing finite threshold theorem then yields C/4 mass of nonexcluded draws with visible score at least C/4. Positive C identifies the threshold event exactly with the nonexcluded visible event; zeroed scores do not qualify.

The actual excluded event comprises drop tail, the draw-dependent completion intersection, fixed-window rank failure, and advice not contained in the retained space. Their masses are bounded by zeta, zeta, twice zeta, and zero respectively. The first and third bounds use GoodAdvice on the actual posterior. The second follows from being outside the exact badPosterior event. The fourth follows directly from the zero kernel and remains true on zero-marginal advice. No independence is assumed.

The actual ready_transfer and mixture identity supply the original posterior mean lower bound. With total margin qdecay(10,h)+loss+4*zeta<=C/2, the resulting theorem concludes actual conditional success mass at least C/4. Its explicit pointwise comparison premise must still be discharged using the actual canonical tables, retained decoded pair and row-frame conditional-agreement identity. This conditional geometric interface does not certify the decoder or source NO. The selected scalar margin and globally legitimate strategy remain separate work. Exact direct parent interfaces match failed/unaccepted Full114; the varying-completion candidate has an immutable pin. No local Lean or Lake ran.

Remaining to-do list: kernel/axiom/warning verification, actual geometric comparison and selected numeric margin, complete strategy/source NO, effective base/runtime, replay and independent/final certification.
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
