from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-hside-selected-charge-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'ActualTaggedComplementIncidence',
                 'ActualTaggedMZSideDraw', 'ActualTaggedFixedCenterGeometry',
                 'SamplerParameters']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for relative, expected in [
    ('numeric-side-extension-formal-offer-20261011-v9/ActualNumericSideExtension.lean',
     '6FFB309A537689B95A751F10F1F35576B0B0196784D464A06BBC8A7E155F0E62'),
    ('numeric-hside-full-zoom-offer-20261011-v2/ActualHSideFullZoom.lean',
     'A7AB365CCC35C6B9D72879DFBE095E41D2DBEDFAAB1E1B45FBC3FB5D46089E6D'),
    ('numeric-robust-cutoffs-offer-v1/ActualNumericRobustCutoffs.lean',
     'E4702CA305CA7316F239A528211B4383FCC664D3C78AEA0CA890334606AED076'),
    ('numeric-robust-real-offer-20261011-v2/ActualNumericRobustReal.lean',
     '3437068369905FDF688E52453245D6EC6E6ECAB1337D741153A618F081650CD7')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidate_deps.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualSelectedHSideAgreement.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert exports == ['selected_actual_hside_full_agreement']
checks = 'import PvNP.RealizableHardness.ActualSelectedHSideAgreement\n\n'
checks += '#print axioms PvNP.RealizableHardness.ActualSelectedHSideAgreement.selected_actual_hside_full_agreement\n'
argument = '''# Selected actual H-side leaf charge

E002/S3137. Complete argument and route assessment were recorded before translation in the existing numeric obligations note, section 2026-10-11 Selected H-side leaf charge and route assessment. This source is uncompiled and unaccepted.

The actual complement witness W',g is extended by the original RHS functional to W=H+W'. The exact H9 dimension identity gives dim(W)+c=3J and the actual question geometry gives dim(H)=J. The same selected numeric floor supplies a<=r,c<=r,8(r+1)<=h and 2J>=8h+4r+16. These imply a<=2h<=dim(W), 2h-a>=1 and J+(2h-a)+1<=dim(W)-a. They also give dim(W)-a-J-(2h-a)-1>=2h+1, paying the exact interval-transversality loss by at most1/2^(2h+1).

The existing selected numeric height yields2/2^(2h)<=e/2; dividing by4 proves the charged loss is at most e/8. The concrete original SideLeaf success/window ratio exceeding e/2 and the actual H-side/full-zoom bridge thus give full agreement greater than3e/8, in particular greater thane/3. Consequently the same fixed rational C<e/3 remains admissible. The theorem takes the actual original SideLeaf agreement as a witness premise: it does not manufacture that premise or replace original-law amplification. No increased height cutoff, new conditional sampling law, independence assumption or decoder strategy is asserted.

Five parent project interfaces match the failed/unaccepted Full114 archive; four candidate dependencies have exact source pins. The public theorem has an explicit axiom request. All sources still require authoritative GCP elaboration, axiom and warning checks after rebinding to an accepted operator parent.

Remaining to-do list: bind actual original-law witnesses to this selected theorem; completion/posterior strategy integration, source NO, full numeric native checks, runtime, replay and all independent/final certification gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    data = path.read_bytes()
    assert not data.startswith(b'\xef\xbb\xbf') and '\ufffd' not in data.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(data), sha256=sha(data)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports)))
