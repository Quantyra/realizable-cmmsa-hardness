from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-global-selected-density-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualTaggedFixedUDensityForce', 'ActualTaggedMZSideDraw',
                 'ActualTaggedOrderedClassCollisionBound', 'ActualTaggedOrderedFullLawForce',
                 'ActualTaggedSelectedDecoderBridge', 'ActualTaggedPresentedSelection',
                 'ActualTaggedComplementStarDensityBridge', 'ActualFiniteLaw']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'
source = (OUT / 'ActualGlobalSelectedDensity.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['∀', '≤', '∃', '∑'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['physical_le_same_choice_mean_plus_collision',
                   'physical_forces_same_choice_high_density',
                   'physical_forces_same_choice_side_density']
checks = 'import PvNP.RealizableHardness.ActualGlobalSelectedDensity\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualGlobalSelectedDensity.' + name + '\n'
                  for name in exports)
plan = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning\docs\research\pvnp\full90-actual-rhs-numeric-no-obligations-2026-10-08.md')
planning = plan.read_text(encoding='utf-8')
heading = '## 2026-10-11 Preserve the representative choice in the global density witness'
assert planning.count(heading) == 1
argument = '# Same representative choice from physical score to side density\n\n'
argument += 'E002/S3137. UNCOMPILED and UNACCEPTED. Implements the argument recorded before translation.\n\n'
argument += planning[planning.index(heading):] + '\n'
argument += ('The exact raw-table representative witness is retained through collision comparison, '
             'the canonical-law equality and all-U side-density transport. No row-count/star-count '
             'binder is identified. The original physical-score, scalar slack and carrier guards '
             'remain explicit for their separate selected-parameter application; no desired decoder '
             'success or source NO assumption is added. GCP and all certification gates remain.\n')
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
    public_axiom_requests=exports, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
