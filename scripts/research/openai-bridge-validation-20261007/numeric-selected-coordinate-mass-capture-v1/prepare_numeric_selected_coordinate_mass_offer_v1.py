from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-selected-coordinate-mass-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
with ARCHIVE.open('rb') as stream:
    assert hashlib.file_digest(stream, 'sha256').hexdigest().upper() == PIN
dependencies = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualFiniteLaw', 'PosteriorDensity', 'PosteriorReweighting']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        dependencies.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    toolchain = archive.extractfile('lean-toolchain').read()
    assert toolchain.decode('utf-8').strip() == 'leanprover/lean4:v4.34.0-rc2'
candidates = []
for relative, pin in [
    ('numeric-fixed-score-conditional-agreement-offer-20261011-v5/ActualFixedScoreConditionalAgreement.lean',
     'CE3A0376B45089946E14DA2E722E9F0D6FDE3087D7134F8A73E27CE178DFB422'),
    ('numeric-fixed-score-conditional-agreement-offer-20261011-v5/ActualFixedScoreVisibleApplication.lean',
     '9F6EF7FDB1C1072C803526522416CD2FBB983FFC004A883576EC2AE43088C601'),
    ('numeric-original-decoder-selection-offer-20261011-v1/ActualOriginalDecoderSelection.lean',
     'EFB5C764DA0A15E9DBFFACF5E366A8D5F20B18F9A687293629F40CED77AD3137'),
    ('numeric-global-selected-density-offer-20261011-v1/ActualGlobalSelectedDensity.lean',
     'A5328B617407F6EAAFB653E8DDAC0861AC077C404E13B2C0A75EC4F25F147652')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == pin, relative
    candidates.append(dict(path=relative, bytes=len(raw), sha256=pin, accepted=False))
capture_path = S / 'numeric-fixed-score-conditional-agreement-capture-v5/index.json'
capture_pin = 'E59EA3953B6BAD164C584E3AED4E4BFD4DC34C20C0F72FD0AB38F9DCE5D12D36'
assert sha(capture_path.read_bytes()) == capture_pin
source = (OUT / 'ActualSelectedCoordinateMass.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(chr(point) in code for point in [0x2200, 0x2264, 0x2203, 0x2211])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['selected_coordinate_mass_eq_original', 'selected_coordinate_decoder_mass',
                   'selected_coordinate_global_dimension', 'physical_forces_global_coordinate_dimension']
checks = 'import PvNP.RealizableHardness.ActualSelectedCoordinateMass\n\n'
for name in exports:
    checks += '#check PvNP.RealizableHardness.ActualSelectedCoordinateMass.' + name + '\n'
    checks += '#print axioms PvNP.RealizableHardness.ActualSelectedCoordinateMass.' + name + '\n'
plan = Path(r'C:\Users\dfred\Desktop\Projects\IGH\Quantyra-AI-Planning\docs\research\pvnp\full90-actual-rhs-numeric-no-obligations-2026-10-08.md')
planning = plan.read_text(encoding='utf-8')
heading = '## 2026-10-11 Original advice mass in one global dimension'
assert planning.count(heading) == 1
argument = '# Actual selected coordinate mass and global dimension\n\n'
argument += 'E002/S3137. UNCOMPILED and UNACCEPTED.\n\n'
argument += planning[planning.index(heading):] + '\n'
argument += ('The four declarations implement the exact uniform-law transport, the original decoder '
             'mass in that frame, finite dimension selection after averaging the original question '
             'law, and its composition with the actual physical-score density theorem. The conclusion '
             'is actual favorable mass, not a supplied or proved final source-game success bound.\n')
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
    fixed_score_v5_capture=dict(path=str(capture_path), sha256=capture_pin, accepted=False),
    planning_argument=dict(path=str(plan), sha256=sha(plan.read_bytes()),
        committed_head='9a9cb09', heading=heading),
    toolchain=dict(value=toolchain.decode('utf-8').strip(), sha256=sha(toolchain)),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_declarations=exports, actual_physical_score_to_favorable_mass=True,
    dimension_fixed_before_question=True, source_game_identified=False, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
