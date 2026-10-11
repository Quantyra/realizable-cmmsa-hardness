"""Pin an actual-row law source offer; performs no Lean invocation."""
from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-row-deletion-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources/lean/PvNP/RealizableHardness'

def digest(raw):
    return hashlib.sha256(raw).hexdigest().upper()

assert not (OUT / 'manifest.json').exists(), 'Never rewrite a stable offer'
assert digest(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualTaggedConcreteStarLaw', 'ActualTaggedFixedCenterGeometry',
                 'ActualStarQuestionSupport', 'ActualStarSpanIntersection',
                 'Finite3LinSource', 'TaggedFinite3LinSource', 'TripleRestrictionRank',
                 'FiniteSampling']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / (name + '.lean')).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=digest(raw)))
source = (OUT / 'ActualTaggedRowDeletion.lean').read_bytes()
code = source.decode('utf-8')
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^(?:def|abbrev) (\w+)', code)
assert len(exports) == 11, exports
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
checks = 'import PvNP.RealizableHardness.ActualTaggedRowDeletion\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualTaggedRowDeletion.' + n + '\n' for n in definitions)
checks += '\n' + ''.join('#print axioms PvNP.RealizableHardness.ActualTaggedRowDeletion.' + n + '\n' for n in exports)
(OUT / 'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# Actual tagged row deletion and its conditional product law

E002/S3137. Complete conditional-on-U argument recorded in the planning numeric note before translation. Uncompiled candidate, no native acceptance.

Fix an actual tagged good question U of J rows. Enumerate its rows by Fin J; combine that bijection with each source row's specified Fin 3 variable positions. Within-row injectivity and disjoint supports prove this map injective, including the empty J case. Every variable in questionSupport belongs to some row, proving surjectivity. The stronger second clause of GoodQuestion is available but not needed for this coordinate fact.

Evaluation at these variables gives a binary linear equivalence from the actual coordinateSpace to TripleRestrictionRank.Vector J. Its inverse extends the coordinate function by zero outside questionSupport. Both inverse equalities are explicit. This frame preserves actual row positions; it is not an arbitrary basis equivalence.

An actual draw assigns BlockChoice to each row of U. Reindexing by the fixed enumeration gives a bijection to Draw J. A variable is retained if its unique row keeps all three positions or the specified singleton position. The row-variable bijection proves both directions of the retained-position equivalence. Therefore a supported vector vanishes outside the actual retained set exactly when its coordinate image belongs to TripleRestrictionRank.retained. Mapping the actualRetained submodule gives exact equality, for each individual draw.

The actual draw weight is the product of the same blockMass beta over actual rows. Reindexing the finite product proves its equality with FiniteSampling.trialMass; reindexing the sum proves equality of every event mass. The weights are nonnegative for 0<=beta<=1 and sum to one. The last theorem composes the pointwise subspace identity with this event identity, giving the pushforward for every event of the retained coordinate subspace.

This source establishes only the conditional law for one fixed actual U. Its coordinate enumeration is a proof device and is not supplied to prover two. The source outer-U marginal, its good-question conditioning loss, choice of completion from only the observed actual variable set, common-leaf exceptional charges, decoder construction and source-NO conclusion remain separate obligations. None is assumed solved by the product-law identity. Full114 is an unaccepted input dependency pin; native scope must rebind to the accepted operator successor.

The eleven public theorem requests cover support membership and injectivity, retained-position and vector equivalences, exact submodule image, draw/event mass reindexing, positivity, normalization and all retained-subspace events. Public definitions are separately checked. No local Lean/Lake execution occurred.

Remaining to-do list: GCP kernel/axiom/warning verification; actual source marginal and global decoder integration; remaining refresh/counting/source/runtime/certification obligations.
'''
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT / '.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for p in sorted(OUT.iterdir()):
    raw = p.read_bytes()
    text = raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in text
    files.append(dict(path=p.name, bytes=len(raw), sha256=digest(raw)))
manifest = dict(schema='numeric-row-deletion-offer-v1', author='/root', story='E002/S3137',
    status='uncompiled', accepted=False, compiler_invoked=False,
    full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    dependencies=deps, public_axiom_requests=exports, checked_definitions=definitions,
    files=files, claims='Exact actual fixed-U row-coordinate frame, retained subspace and all-event product-law transport; outer source law and decoder unresolved.')
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=digest(source), checks_sha256=digest(checks.encode()),
    manifest_sha256=digest((OUT/'manifest.json').read_bytes()), dependencies=len(deps), exports=exports), indent=2))
