from pathlib import Path
import hashlib
import json
import re
import subprocess
import tarfile

S = Path(__file__).resolve().parent
P = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning')
OUT = S / 'numeric-full-advice-prefix-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
dependencies = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['VectorAdvice', 'CoveringSpan', 'SamplerParameters']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'
mathlib_sources = []
for relative in ['Logic/Equiv/Fin/Basic.lean', 'Logic/Equiv/Prod.lean']:
    path = REF / 'external/Mathlib' / relative
    raw = path.read_bytes()
    mathlib_sources.append(dict(path=str(path), module='Mathlib.' + relative[:-5].replace('/', '.'),
        bytes=len(raw), sha256=sha(raw)))
candidates = []
for relative, pin in [
    ('numeric-visible-vector-advice-offer-20261011-v1/ActualVisibleVectorAdvice.lean',
     '4DA07033495C40FF7336B4DE887FB47C18C8729285C13B9A6D91270CD58C368F'),
    ('numeric-visible-joint-success-offer-20261011-v1/ActualVisibleJointSuccess.lean',
     '3460990232404322ADB2AC1774500B304350D4F90206A50019BB26BDB2057EB9')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == pin, relative
    candidates.append(dict(path=relative, bytes=len(raw), sha256=pin, accepted=False))
capture_path = S / 'numeric-visible-vector-advice-capture-v1/index.json'
capture_pin = '7C212024F75ED766B27710EFDD83D8156D0A738A622250401838AE3BC8990100'
assert sha(capture_path.read_bytes()) == capture_pin
source = (OUT / 'ActualFullAdvicePrefix.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(chr(point) in code for point in [0x2264, 0x2211, 0x2243])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['uniform_prefix_mean', 'fullAdviceJointScore_eq', 'visible_joint_event_full_advice_transfer']
assert definitions == ['advicePrefix', 'fullAdviceJointScore']
checks = 'import PvNP.RealizableHardness.ActualFullAdvicePrefix\n\n'
for name in definitions + exports:
    checks += '#check PvNP.RealizableHardness.ActualFullAdvicePrefix.' + name + '\n'
for name in exports:
    checks += '#print axioms PvNP.RealizableHardness.ActualFullAdvicePrefix.' + name + '\n'
relative_plan = 'docs/research/pvnp/full90-actual-rhs-numeric-no-obligations-2026-10-08.md'
committed_plan = subprocess.run(['git', '-C', str(P), 'show', '35ce298:' + relative_plan],
    check=True, stdout=subprocess.PIPE).stdout
heading = '## 2026-10-11 The full supplied advice tuple and its used prefix'
planning = committed_plan.decode('utf-8')
assert planning.count(heading) == 1
section = planning[planning.index(heading):]
argument = '# Full supplied-array prefix marginal\n\nE002/S3137. UNCOMPILED and UNACCEPTED.\n\n' + section + '\n'
argument += ('This module translates the exact uniform prefix expectation and applies it to the '
             'literal visible joint event. It does not test unused vectors for independence, '
             'resample a failed used prefix, or add a second error charge. Actual coordinate/output '
             'and source-game acceptance identification remains open.\n')
for name, data in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(data, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN, accepted=False),
    dependencies=dependencies, candidate_dependencies=candidates,
    vector_capture=dict(path=str(capture_path), sha256=capture_pin, accepted=False),
    planning_argument=dict(repository=str(P), relative_path=relative_plan, committed_head='35ce298',
        committed_blob_sha256=sha(committed_plan), heading=heading, section_sha256=sha(section.encode())),
    toolchain=dict(value=toolchain.decode('utf-8').strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', mathlib_source_dependencies=mathlib_sources,
    public_axiom_requests=exports, checked_definitions=definitions,
    full_supplied_array=True, unused_entries_conditioned=False, source_game_identified=False, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports, definitions=definitions)))
