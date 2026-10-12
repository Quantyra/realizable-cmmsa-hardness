from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-visible-vector-advice-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
dependencies = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['VectorAdvice', 'SamplerParameters']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'
relative = 'numeric-visible-joint-success-offer-20261011-v1/ActualVisibleJointSuccess.lean'
raw = (S / relative).read_bytes()
assert sha(raw) == '3460990232404322ADB2AC1774500B304350D4F90206A50019BB26BDB2057EB9'
candidates = [dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False)]
source = (OUT / 'ActualVisibleVectorAdvice.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(chr(point) in code for point in [0x2200, 0x2264])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['visible_joint_event_vector_transfer']
checks = 'import PvNP.RealizableHardness.ActualVisibleVectorAdvice\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualVisibleVectorAdvice.' + name + '\n'
                  for name in exports)
plan = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning\docs\research\pvnp\full90-actual-rhs-numeric-no-obligations-2026-10-08.md')
planning = plan.read_text(encoding='utf-8')
heading = '## 2026-10-11 Global strategy and actual vector-advice composition'
assert planning.count(heading) == 1
argument = '# Literal visible-event vector-advice correction\n\n'
argument += 'E002/S3137. UNCOMPILED and UNACCEPTED.\n\n'
argument += planning[planning.index(heading):] + '\n'
argument += ('This source implements only the literal visible-event correction in the third paragraph. '
             'It uses the actual jointVisibleSuccess and the pinned generic vector-law loss, '
             'not the older event-specific decoder theorem. Actual acceptance-law identification, '
             'dimension averaging, imported count, source NO and native certification remain open.\n')
for name, data in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(data, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=dependencies, candidate_dependencies=candidates,
    toolchain=dict(value=toolchain.decode('utf-8').strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    literal_visible_event=True, source_game_identified=False, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
