from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S/'numeric-transverse-agreement-loss-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S/'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'RobustSourceLineContainment',
                 'GrassmannCounting', 'GrassmannFlagPosterior']:
        member = 'lean/PvNP/RealizableHardness/'+name+'.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF/member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
source = (OUT/'ActualTransverseAgreementLoss.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 4, exports
assert len(definitions) == 3, definitions
checks = 'import PvNP.RealizableHardness.ActualTransverseAgreementLoss\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualTransverseAgreementLoss.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualTransverseAgreementLoss.'+n+'\n' for n in exports)
argument = '''# Removing actual full-zoom transversality conditioning

E002/S3137. The complete mathematical argument was recorded before translation in the planning numeric obligations note under 2026-10-11 Removing leaf transversality conditioning: exact argument. This is uncompiled and unaccepted.

For the same actual table T and decoded pair P over Q, define transverseZoom as the finite subset of the complete Zoom(Q,P) where L intersects H trivially. transverseAgreement is the literal number of agreeing transverse leaves divided by its cardinality. transverseExceptionFraction is the complementary cardinality divided by the full zoom cardinality. No event-mass hypothesis is substituted for these counts.

Let u count agreeing transverse leaves, s count all agreeing leaves, g count transverse leaves, b count the complement and n count the full zoom. Then u<=s, u<=g, g+b=n. If g=0, u=0 and the desired inequality is immediate with zero-denominator conventions. Otherwise n>0 and multiplying by g*n reduces u/g-b/n<=s/n to u*(g+b)<=s*g+g*b, which follows from u<=s and u<=g. The actual agreement definition equals its full zoom cardinality ratio even when that carrier is empty. This proves full agreement at least conditional transverse agreement minus the actual exceptional fraction.

For the count bound assume H<=P.W, Q disjoint from H, a<=d<=dim(P.W), d-a>=1, and dim(H)+(d-a)+1<=dim(P.W)-a. The exact relativeUpperEquiv identifies the full Zoom with the interval above the same Q inside P.W. The comapSubtypeEquivOfLe preserves dim(H). The subtype injection preserves the zero/nonzero intersection predicate in both directions, so an event-subtype equivalence identifies the bad numerator and the whole-carrier equivalence identifies the denominator. Applying the pinned intervalTransverseException_mass_le_dyadic gives the exact charge 1/2^(dim(P.W)-a-dim(H)-(d-a)-1). Substitution yields the public full-agreement lower bound.

This closes the abstract full-zoom charge with explicit actual carriers and dimensions. It still needs the H-side canonical-table ratio identification and selected numeric specialization to yield the source decoder's rational agreement threshold. The later visible-completion table comparison and posterior joint bound are distinct obligations. It does not claim equality on nontransverse leaves, source NO, or full certification.

Four project dependencies match Full114 archive members. Four public theorem axiom requests and three definition checks are included. No local Lean/Lake ran; all source dependencies must be rebound to an accepted operator parent for authoritative GCP verification.

Remaining to-do list: GCP kernel/axiom/no-regression checks, concrete H-side ratio and numeric charge, completion/posterior decoder integration and all source-NO/runtime/certification gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT/name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False, compiler_invoked=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN), dependencies=deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
