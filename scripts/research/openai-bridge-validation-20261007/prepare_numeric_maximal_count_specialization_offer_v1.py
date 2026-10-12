from pathlib import Path
import hashlib
import json
import re
import subprocess
import tarfile

S = Path(__file__).resolve().parent
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
OUT = S / 'numeric-maximal-count-specialization-offer-20261011-v1'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
sha = lambda data: hashlib.sha256(data).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
dependencies = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['DropTailParameters', 'ActualMaximalPairLadder', 'GrassmannCounting',
                 'ActualCmmsaParameterReconciliation']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode().strip() == 'leanprover/lean4:v4.34.0-rc2'
candidates = []
for stem, version, name, expected, cap_expected in [
    ('maximal-count-guards', 1, 'ActualMaximalCountGuards',
     '6C01F6A58BAC0645D307EB9B7436568E00DA79171448C0C1D06696E92D1D1647',
     '037BE52EAC655132616E606E96BF9041844C14976ADAE4E4A72E8FDDBC5C4AA4'),
    ('robust-real', 2, 'ActualNumericRobustReal',
     '3437068369905FDF688E52453245D6EC6E6ECAB1337D741153A618F081650CD7',
     'DC64C94F879644D867BBFD601E1279B1FBEF28D3C1C1C58E559D0E7378E5CDF8'),
    ('visible-list-strategy', 1, 'ActualVisibleListStrategy',
     '1E7176008530D5D0BB0DEE16C428A295FFD08E6CB7BFEC34F0BAFEE46DC85D77',
     'CDE6A543F13319B4E65181890DEC3490A253B5D4CDC94AE96A1A30073E6A0A65')]:
    candidate = S / f'numeric-{stem}-offer-20261011-v{version}' / (name + '.lean')
    capture = S / f'numeric-{stem}-capture-v{version}'
    raw = candidate.read_bytes()
    assert sha(raw) == expected and raw == (capture / candidate.name).read_bytes()
    assert sha((capture / 'index.json').read_bytes()) == cap_expected
    candidates.append(dict(path=str(candidate), bytes=len(raw), sha256=expected,
        capture_path=str(capture / 'index.json'), capture_sha256=cap_expected,
        accepted=False))
mathlib = []
for relative in ['Algebra/Order/GroupWithZero/Basic.lean', 'Algebra/Group/DivInvMonoid.lean']:
    path = REF / 'external/Mathlib' / relative
    raw = path.read_bytes()
    mathlib.append(dict(path=str(path), bytes=len(raw), sha256=sha(raw)))
readback = S / 'numeric-count-import-readback-20261011-v1/source-readback.json'
assert sha(readback.read_bytes()) == '39DC568877302A7ED7A6856559F659F70F0EBAFFF33F016932B4FF94816A21D6'
source = (OUT / 'ActualMaximalCountSpecialization.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf')
assert all(marker not in code for marker in ['\ufffd', '\u00e2\u02c6', '\u00e2\u2020', '\\sum'])
assert all(chr(n) in code for n in [0x2264, 0x2190, 0x2227])
# Lexical delimiter/placeholder preflight is source-only, not a Lean parse.
stack, visible = [], []
depth = 0
quoted = False
i = 0
while i < len(code):
    pair = code[i:i+2]
    if depth:
        if pair == '/-': depth += 1; i += 2; continue
        if pair == '-/': depth -= 1; i += 2; continue
        i += 1; continue
    if quoted:
        if code[i] == '\\': i += 2; continue
        if code[i] == '"': quoted = False
        i += 1; continue
    if pair == '/-': depth = 1; i += 2; continue
    if pair == '--':
        end = code.find('\n', i)
        i = len(code) if end < 0 else end
        continue
    if code[i] == '"': quoted = True; i += 1; continue
    visible.append(code[i])
    if code[i] in '([{': stack.append((code[i], i))
    if code[i] in ')]}':
        assert stack and stack[-1][0] == {')': '(', ']': '[', '}': '{'}[code[i]], i
        stack.pop()
    i += 1
assert not stack and not depth and not quoted
assert not re.search(r'\b(?:sorry|admit|axiom)\b', ''.join(visible))
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['reciprocal_source_parameters', 'actual_level_count_of_declared_contract',
    'combinedCountCost_pos', 'combined_count_cost_le_dyadic', 'count_cost_retains_decay9']
assert definitions == ['countReciprocal', 'countSourceT', 'countLinearExponent',
    'countConstant', 'countExponent', 'combinedCountCost', 'countCostHeight']
checks = 'import PvNP.RealizableHardness.ActualMaximalCountSpecialization\n\n'
for name in definitions + exports:
    checks += '#check PvNP.RealizableHardness.ActualMaximalCountSpecialization.' + name + '\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualMaximalCountSpecialization.' + name + '\n'
relative_plan = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
plan_raw = subprocess.run(['git', '-C', str(P), 'show', 'bf968d0:' + relative_plan],
                          check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 Exact reciprocal specialization of the declared counting import'
plan = plan_raw.decode('utf-8')
assert plan.count(heading) == 1
section = plan[plan.index(heading):].split('\n## ', 1)[0]
argument = '# Declared count specialization and fixed-index cost\n\nE002/S3137. UNCOMPILED and UNACCEPTED.\n\n'
argument += section + '\n\n'
argument += ('The hImported premise remains the exact all-window imported count at the '
             'actual level. This module does not prove the source theorem or bind all its '
             'hypotheses to visible questions. It supplies no assumed final game-success '
             'probability. The reciprocal identities, level-threshold denominator bound, '
             'positive fixed cost, natural height absorption, and D8-to-D9 scalar '
             'implication are the five translation steps. Actual game identification '
             'and every external cutoff/applicability condition remain required.\n')
for name, data in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(data, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    assert path.is_file(), path
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, story='E002/S3137', author='/root', accepted=False,
    compiler_invoked=False, source_only_lexical_preflight=True,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN, accepted=False),
    dependencies=dependencies, candidate_dependencies=candidates,
    planning_argument=dict(repository=str(P), relative_path=relative_plan, committed_head='bf968d0',
        committed_blob_sha256=sha(plan_raw), heading=heading, section_sha256=sha(section.encode())),
    primary_source_readback=dict(path=str(readback), sha256=sha(readback.read_bytes())),
    toolchain=dict(value=toolchain.decode().strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', mathlib_source_dependencies=mathlib,
    mathlib_tactic_hub_source_locally_available=False,
    mathlib_tactic_binding='Pinned Mathlib revision; local source excerpt unavailable, verify on GCP.',
    public_axiom_requests=exports, checked_definitions=definitions,
    exact_reciprocal_natural_constants=True, external_count_is_explicit_hypothesis=True,
    external_count_locally_proved=False, external_count_actual_applicability_proved=False,
    game_law_identified=False, source_no_proved=False, effective_uniform_cutoff_inferred=False,
    files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()),
    public_theorems=len(exports), checked_definitions=len(definitions))))
