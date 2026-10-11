from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S/'numeric-random-extension-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S/'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualStarAffineFunctionalSelection', 'SubmoduleFunctionalGluing',
                 'ActualFiniteLaw', 'ActualMaximalPairLadder']:
        member = 'lean/PvNP/RealizableHardness/'+name+'.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF/member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
mathlib = []
for member in ['external/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean',
               'external/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean']:
    raw = (REF/member).read_bytes()
    mathlib.append(dict(path=member, bytes=len(raw), sha256=sha(raw)))
source = (OUT/'ActualRandomExtensionSuccess.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 7, exports
assert len(definitions) == 2, definitions
checks = 'import PvNP.RealizableHardness.ActualRandomExtensionSuccess\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualRandomExtensionSuccess.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualRandomExtensionSuccess.'+n+'\n' for n in exports)
argument = '''# Exact random-extension success on the actual affine fiber

E002/S3137. The complete mathematical argument was recorded in the planning numeric obligations note under 2026-10-11 Exact random-extension success argument before translation. This source is uncompiled and unaccepted.

Fix actual subspaces W,V of a finite binary ambient E and an actual functional g on W. The retained-rank event states dim(V)-dim(W intersect V)=dim(E)-dim(W). Subspace dimension bounds and dimension addition imply dim(W+V)=dim(E), so W+V=E. For any actual functional f on V compatible with g on W intersect V, unique gluing on W+V supplies an ambient extension with both restrictions. Uniqueness is also proved directly by decomposing every x in E as w+v and using both restrictions. Thus the actual event inside FunctionalExtensionFiber W g of restricting to f has exactly one member.

The sampling law is uniform on the complete actual affine fiber of ambient extensions of g; nonemptiness is constructed from LinearMap.exists_extend. The pinned functionalExtensionFiber_card gives cardinality 2^(dim(E)-dim(W)). The singleton event therefore has mass exactly 1/2^codim(W), and at least 1/2^r if codim(W)<=r. No conditioning on a successful extension occurs. The compatible f may be selected using all the visible data on V: the calculation is pointwise in f, with no independence assertion about that selection.

Every extension agrees with g on W, so whenever H<=W and g restricts to rhs on H, every sampled extension also restricts to rhs. This is the exact row-satisfaction step once H is the actual equation span and the first prover's chosen pair respects its right-hand sides. Compatibility and retained-rank equality remain explicit premises here; the actual posterior event, ladder and list selection must supply them when assembling the decoder. This does not itself construct a full source-game strategy or prove a NO bound.

Four project sources match exact Full114 archive members. Two Mathlib reference source hashes and the pinned revision are recorded for API provenance; the authoritative complete Mathlib closure remains the GCP package's responsibility. Seven theorem axiom requests and two definition checks are included. No Lean or Lake was run locally. Full114 is not accepted, and eventual compilation must bind the complete source closure to the accepted operator parent.

Remaining to-do list: GCP kernel/axiom/warning verification; actual posterior/ladder and row-assignment integration; full source decoder/NO, runtime, random-history and certification gates.
'''
for name, content in [('Checks.lean', checks), ('ARGUMENT.md', argument), ('.gitattributes', '* -text\n')]:
    (OUT/name).write_text(content, encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema=OUT.name, author='/root', story='E002/S3137', accepted=False, compiler_invoked=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN), dependencies=deps, mathlib_reference_sources=mathlib,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
