from pathlib import Path
import hashlib
import json
import re
import subprocess
import tarfile
from fractions import Fraction

S = Path(__file__).resolve().parent
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
OUT = S / 'numeric-global-decoder-scalar-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
dependencies = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['DropTailParameters', 'ActualStarAcceptedGoodMass',
                 'ActualStarFixedRhoDimensionGuard', 'ActualCmmsaParameterReconciliation']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
candidate = S / 'numeric-robust-real-offer-20261011-v2/ActualNumericRobustReal.lean'
capture = S / 'numeric-robust-real-capture-v2/index.json'
captured_source = S / 'numeric-robust-real-capture-v2/ActualNumericRobustReal.lean'
assert candidate.read_bytes() == captured_source.read_bytes()
mathlib = []
for relative in ['Analysis/SpecialFunctions/Pow/Real.lean',
                 'Algebra/Order/GroupWithZero/Basic.lean']:
    path = REF / 'external/Mathlib' / relative
    raw = path.read_bytes()
    mathlib.append(dict(path=str(path), bytes=len(raw), sha256=sha(raw)))
source = (OUT / 'ActualGlobalDecoderScalar.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf')
assert all(marker not in code for marker in ['\ufffd', '\u00e2\u02c6', '\u00e2\u2020', '\\sum'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
assert all(chr(n) in code for n in [0x2264, 0x2190])
# Remove nested comments and quoted strings before checking source delimiters.
stack = []
depth = 0
quoted = False
i = 0
while i < len(code):
    if depth:
        if code[i:i+2] == '/-': depth += 1; i += 2; continue
        if code[i:i+2] == '-/': depth -= 1; i += 2; continue
        i += 1; continue
    if quoted:
        if code[i] == '\\': i += 2; continue
        if code[i] == '"': quoted = False
        i += 1; continue
    if code[i:i+2] == '/-': depth = 1; i += 2; continue
    if code[i:i+2] == '--':
        i = code.find('\n', i)
        if i < 0: i = len(code)
        continue
    if code[i] == '"': quoted = True; i += 1; continue
    if code[i] in '([{': stack.append((code[i], i))
    if code[i] in ')]}':
        assert stack and stack[-1][0] == {')': '(', ']': '[', '}': '{'}[code[i]], i
        stack.pop()
    i += 1
assert not stack and not depth and not quoted
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['actual_threshold_lower', 'actual_posterior_floor_lower',
                   'actual_full_vector_loss_le', 'actual_posterior_floor_sub_vector_lower']
assert definitions == ['posteriorFloor']
checks = 'import PvNP.RealizableHardness.ActualGlobalDecoderScalar\n\n'
for name in definitions + exports:
    checks += '#check PvNP.RealizableHardness.ActualGlobalDecoderScalar.' + name + '\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualGlobalDecoderScalar.' + name + '\n'
relative_plan = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan_raw = subprocess.run(['git', '-C', str(P), 'show', '3d4c03c:' + relative_plan],
                          check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Global error absorption at the same selected height'
plan = plan_raw.decode('utf-8')
assert plan.count(heading) == 1
section = plan[plan.index(heading):].split('\n## ', 1)[0]
argument = '# Actual global posterior scalar absorption\n\nE002/S3137. UNCOMPILED and UNACCEPTED.\n\n'
argument += section + '\n\n'
argument += ('This candidate translates the fixed-threshold lower bound, actual natural badExponent '
             'and successMargin bound, global error absorption, and exactly one full-vector loss. '
             'It does not supply the actual posterior inequality, game acceptance, imported count, '
             'or final source NO as an assumed probability. Its public theorem is a scalar '
             'inequality for the explicit posteriorFloor expression. Binding this expression to '
             'the global posterior result and discharging every same-index guard remain required.\n')
# Exact rational boundary checks examine the joint linear-cost absorption;
# they are arithmetic cross-checks only, not Lean or probability certification.
cases = []
for m in [0, 1, 2, 3, 5, 8, 12]:
    for h in [2*m+4, 2*m+5, 2*m+9]:
        for r in sorted({0, h//2, h}):
            d = lambda k: Fraction(1, 2 ** (k * h*h))
            margin = Fraction(1, 2 ** (2*m*h))
            threshold = Fraction(1, 2 ** (2*h+3))
            value = (d(6)/(r+1)*8*margin-d(20)-d(69)-d(20)/3)*(threshold/4)
            assert d(7) <= value
            assert d(8) <= value-d(100)
            cases.append(dict(m=m, r=r, h=h, posterior=True, vector=True))
verification = dict(kind='exact-rational-boundary-cross-check', accepted=False,
    compiler_invoked=False, worst_case_linear_margin=True, minimum_dyadic_threshold=True,
    count=len(cases), cases=cases)
for name, data in [('Checks.lean', checks), ('ARGUMENT.md', argument),
                   ('arithmetic-cross-check.json', json.dumps(verification, indent=2)+'\n'),
                   ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(data, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    assert path.is_file(), path
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, story='E002/S3137', author='/root', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN, accepted=False),
    dependencies=dependencies, candidate_dependencies=[dict(path=str(candidate),
        sha256=sha(candidate.read_bytes()), capture_path=str(capture),
        capture_sha256=sha(capture.read_bytes()), accepted=False)],
    planning_argument=dict(repository=str(P), relative_path=relative_plan, committed_head='3d4c03c',
        committed_blob_sha256=sha(plan_raw), heading=heading, section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', mathlib_source_dependencies=mathlib,
    mathlib_tactic_hub_source_locally_available=False,
    mathlib_tactic_binding='Pinned Mathlib revision; local source excerpt unavailable, verify on GCP.',
    public_axiom_requests=exports, checked_definitions=definitions,
    actual_badExponent=True, actual_successMargin=True, actual_refreshThreshold=True,
    explicit_same_height_guards=True, game_law_identified=False, source_no_proved=False, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),
    candidate_dependency_sha256=sha(candidate.read_bytes()),
    candidate_capture_sha256=sha(capture.read_bytes()), arithmetic_cases=len(cases))))
