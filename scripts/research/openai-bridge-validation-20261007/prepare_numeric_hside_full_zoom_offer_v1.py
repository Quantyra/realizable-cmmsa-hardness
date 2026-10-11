from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-hside-full-zoom-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'ActualTaggedComplementIncidence',
                 'ActualTaggedMZSideDraw', 'ActualTaggedSelectedDecoderBridge',
                 'ActualTaggedPresentedSelection', 'ActualFiniteLaw',
                 'ActualTaggedFixedCenterGeometry', 'ActualStarSpanIntersection']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for relative, expected in [
    ('numeric-side-extension-formal-offer-20261011-v9/ActualNumericSideExtension.lean',
     '6FFB309A537689B95A751F10F1F35576B0B0196784D464A06BBC8A7E155F0E62'),
    ('numeric-transverse-agreement-loss-offer-20261011-v1/ActualTransverseAgreementLoss.lean',
     'BCC8D7D4F5B71A4AC4A11CD00B5F0A7BB965628AFD63330A6519B968D09FFE74')]:
    raw = (S / relative).read_bytes()
    assert sha(raw) == expected
    candidate_deps.append(dict(path=relative, bytes=len(raw), sha256=sha(raw), accepted=False))
source = (OUT / 'ActualHSideFullZoom.lean').read_bytes()
code = source.decode('utf-8')
assert not source.startswith(b'\xef\xbb\xbf')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
assert '\ufffd' not in code and all(x in code for x in ['⊓', '⊔', '→ₗ', '≤', '↔'])
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 3 and len(definitions) == 3
checks = 'import PvNP.RealizableHardness.ActualHSideFullZoom\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualHSideFullZoom.' + n + '\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualHSideFullZoom.' + n + '\n' for n in exports)
argument = '''# Actual H-side to full-zoom table identity

E002/S3137. The complete mathematical argument was recorded before translation in the planning numeric obligations note, section 2026-10-11 Actual H-side to full-zoom table identity. Source is uncompiled and unaccepted.

The total leaf table uses the same global canonical selected table on the image of H+L and restricts it to L. It is independent of advice K and successful complement A. The decoded pair uses the actual H+W' window and canonical RHS extension of g. Global SideLeaf transversality is equivalent to internal disjointness by injectivity of the actual coordinate inclusion, in both directions. Bounded SideLeaf and transverse full Zoom are therefore bijective on the underlying Grassmann leaf. Containment of H+L in a window containing H is equivalent to containment of L.

Pointwise restriction agreement is the same functional equality on each included leaf vector. Reindexing that event and the whole bounded carrier proves equality of their count ratios. The original k=1 uniform SideLeaf event masses reduce to these counts because their common, nonzero carrier cardinality cancels. Empty bounded windows require no nonemptiness premise and use the existing zero-division convention. Substituting the previous full-zoom dyadic charge proves the final agreement lower bound on the same total table and actual decoder, with the dimension guards explicit.

The ordinary-to-SideLeaf ratio is supplied separately by the frozen H9 candidate. Selected numerical guards, its actual successful ordinary witness, visible-input table equality, posterior errors and complete source decoder remain integration obligations. This source neither asserts equality on exceptional leaves nor certifies any parent. Eight source interfaces match the exact failed/unaccepted Full114 archive, and both new candidate dependencies have exact frozen hashes. Three public theorem axiom requests and three definition checks are provided. No Lean or Lake was executed locally.

Remaining to-do list: authoritative GCP kernel/axiom/warning checks, ordinary witness and numeric specialization, completion/posterior decoder integration, source NO, runtime and all mandatory review/certification gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT / name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False,
    compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT / 'manifest.json').read_bytes()), exports=exports), indent=2))
