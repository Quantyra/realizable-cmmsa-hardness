from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-varying-coefficient-base-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualCmmsaAdmissibilitySelector', 'ActualCmmsaParameterReconciliation',
                 'GoodAdvice', 'SamplerParameters', 'SamplerProximity']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'
candidates = []
for relative, expected in [
    ('numeric-varying-completion-exception-offer-20261011-v7/ActualSelectedCompletionPosteriorBound.lean',
     'BA0B71DD1230F84145F13C34D758C731C0E327502FBCCD400974BEDCDD6AE0CC'),
    ('numeric-explicit-height-offer-capture-v3/ActualNumericExplicitHeight.lean',
     'B255244AE3D98413B943278A8C17E5099FAB876573E8E62A530093955D898847'),
    ('numeric-source-height-offer-capture-v3/ActualNumericSourceHeight.lean',
     '98661E33A9C272CB983368B60C12BF7AA7BE833076A5545CAB1CDF4917209BDF')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidates.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualVaryingCoefficientBase.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['∀', '≤', '∃', 'ℚ'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['pointwiseCommonBase_bounds', 'pointwise_completion_bound',
                   'selected_varying_completion_eventually']
assert definitions == ['pointwiseCommonBase']
checks = 'import PvNP.RealizableHardness.ActualVaryingCoefficientBase\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVaryingCoefficientBase.' + name + '\n'
                  for name in definitions + exports)
argument = '''# Varying sampler coefficient at the same selected index

E002/S3137. Implements the recorded Common-base quantifiers and fixed-parameter effectiveness argument. Uncompiled and unaccepted.

For each candidate j, fix its positive natural coefficient A_j and use the already captured selectedCommonBase at A_j and rank cap R_j. This gives a single natural-valued floor whose j-th value dominates base0(j), NP(A_j,R_j), NT(A_j), R_j and16. A height exceeding that same value supplies actual sampler readiness and the actual completion-posterior estimate at A_j, without a supplied exceptional-mass premise.

Apply the existing selector existence theorem to this actual pointwise floor. Its temporary A=1 argument is used only to obtain existence and the base-height conclusion, which is independent of the subsequent coefficient; no block estimate from A=1 is reused. The returned m and h dominate the pointwise floor at m. The preceding generic actual completion theorem therefore applies at A_m. The final statement retains selector equality, any requested lower bound M on m, actual readiness, and the all-U/all-a completion mass estimate under that same tuple. No selector witness from a smaller or constant-coefficient floor is substituted.

These classical finite thresholds alone do not give a computable uniform map from L to a reduction program. The manuscript promises only a uniform polynomial-time reduction on instances for each separately fixed L, allowing its finitely many chosen parameters to be fixed program constants. That quantifier observation does not supply the full source floor or encoded runtime proof. base0 and cutoff still need the remaining same-index source/scalar thresholds, and the actual strategy/NO argument and encoded construction remain open. Parent Full114 and candidate dependencies retain failed/unaccepted or source-only status; accepted operator rebinding and GCP verification are required. No local Lean or Lake ran.

Remaining to-do list: kernel/axiom/warning verification, full same-index source floor and actual strategy/source NO, fixed-parameter encoded runtime/learning, replay and independent/final certification gates.
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
    toolchain=dict(value=toolchain.decode('utf-8').strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports,
    checked_definitions=definitions)))
