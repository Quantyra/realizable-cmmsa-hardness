from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-original-decoder-selection-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['PosteriorReweighting', 'GrassmannCounting', 'ActualMaximalPairLadder']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidates = []
for relative, expected in [
    ('numeric-original-law-full-decoder-integration-offer-v2/ActualOriginalLawFullDecoderIntegration.lean',
     'AD361FE8CFF01B286F6C8BCD8DA7955A2F801FB0C151352EC7AD9F247C064CB6'),
    ('numeric-row-deletion-offer-20261011-v1/ActualTaggedRowDeletion.lean',
     'F844D422FEF025399462872F9F59D6EC1E8BA41C28DCE4D95B20C463B876390B')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidates.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualOriginalDecoderSelection.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert all(glyph in code for glyph in ['∑', '≤', '∃', '⊓', 'ℚ'])
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert exports == ['selectedPair_properties', 'originalAdviceMass_normalized',
    'favorable_mass_eq_ratio', 'selected_original_decoder_mass', 'favorable_selectedPair_agreement']
assert definitions == ['defaultPair', 'selectedPair', 'favorable', 'originalAdviceMass']
checks = 'import PvNP.RealizableHardness.ActualOriginalDecoderSelection\n\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualOriginalDecoderSelection.' + name + '\n'
                  for name in definitions + exports)
argument = '''# Actual original decoder selection

E002/S3137. Implements the recorded 2026-10-11 Selecting the actual original decoded pair argument. Uncompiled and unaccepted.

On the actual full-decoder favorable event, select the named-advice decoded pair supplied by the original-law endpoint. Its window contains the original H, its functional restricts to the actual canonical RHS on H, its codimension is at most r, and its canonical full-table agreement exceeds e/3. On other advice use a whole-space zero pair to make the selection total. No equation satisfaction or success is claimed for that default. This function depends on original U, the fixed table and Q, not the deletion draw.

The actual original-law theorem supplies a dimension a<=r whose favorable carrier ratio is at least 2^(-6*h^2). The actual row-coordinate equivalence proves ambient dimension3J. GrassmannCounting.card_grass therefore identifies its full carrier cardinality with the precise Gaussian denominator, so summing uniform original-advice weights gives exactly the same favorable ratio. Normalization is separately established under a<=3J. The rational threshold C<e/3 is met by all favorable selected pairs. No favorable mass or independent decoded witness is supplied as a premise; the input is the actual conditional star density used by the original amplification theorem.

This realizes the original-pair side of the joint-law decoder interface. The whole selection, table and event still require row-frame transport and the fixed-score identity before being supplied to the joint-law theorem. The visible pointwise comparison, maximal-list strategy, random extensions and actual outer source-game law remain separate obligations. Parent interfaces are exact failed/unaccepted Full114 pins; full-decoder V2 and actual row deletion are immutable candidate dependencies. No local Lean or Lake ran.

Remaining to-do list: kernel/axiom/warning verification, actual row-frame/posterior instantiation, maximal-list/strategy/source NO, effective base/runtime, replay and independent/final certification.
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
