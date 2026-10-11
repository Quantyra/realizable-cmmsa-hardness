from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-distinct-advice-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['GrassmannCounting', 'GrassmannFlagPosterior', 'ActualMaximalPairLadder']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF/member).read_bytes()
        deps.append(dict(member=member, sha256=sha(raw), bytes=len(raw)))
    parent = json.load(archive.extractfile('capture-manifest.json'))
external = []
for name in ['Mathlib/Algebra/Order/BigOperators/Group/Finset.lean',
             'Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean',
             'Mathlib/Data/Fintype/Card.lean',
             'Mathlib/Algebra/Order/GroupWithZero/Basic.lean']:
    raw = (REF/'external'/name).read_bytes()
    member = '.lake/packages/mathlib/' + name
    assert sha(raw) == parent['cache_provenance']['package_sources'][member]
    external.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
candidate_deps = []
for folder, file, module, pin in [
    ('numeric-refresh-cover-offer-20261011-v1', 'ActualRefreshGoodCover.lean', 'ActualRefreshGoodCover', 'F42880569F78847DD4AD7AA4A3572C309AD76F3A1D8CA8ACF6CC9EB6AFCD12EB'),
    ('numeric-refresh-formal-offer-20261011-v1', 'ExactRefresh.lean', 'NumericRefreshFormalOffer', 'B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3')]:
    path = S/folder/file
    raw = path.read_bytes()
    assert sha(raw) == pin
    candidate_deps.append(dict(path=str(path), sha256=pin, bytes=len(raw), module=module, status='uncompiled'))
capture = S/'numeric-refresh-history-capture-v1'
index = json.loads((capture/'index.json').read_bytes())
row = next(x for x in index['files'] if x['copy'] == 'ActualRefreshCandidates.lean')
path = capture/row['copy']
raw = path.read_bytes()
assert sha(raw) == row['sha256']
candidate_deps.append(dict(path=str(path), sha256=sha(raw), bytes=len(raw),
    module='ActualRefreshCandidates', status='uncompiled', capture_index_sha256=sha((capture/'index.json').read_bytes())))
source = (OUT/'ActualDistinctAdviceCoverage.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 11
assert len(definitions) == 4
checks = 'import PvNP.RealizableHardness.ActualDistinctAdviceCoverage\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualDistinctAdviceCoverage.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualDistinctAdviceCoverage.'+n+'\n' for n in exports)
(OUT/'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# Distinct advice coverage by exact Grassmann incidence

E002/S3137. The complete argument was recorded before translation at planning commit 50e29d8 in the numeric obligations note, section 2026-10-11 Distinct-advice incidence argument. This is an uncompiled source candidate, not a certified result.

For each a in Fin(r+1), goodAdvice is the finite set of actual Q admitting P with a+codim(P.W)=r and original agreement greater than e/2. A Q occurs once regardless of its number of decoded witnesses W,g. Membership is characterized with the exact existential; fractions are the actual card divided by card(Grass V a), nonnegative and at most one even for an empty ambient stratum.

Every leaf in the actual originalGoodZoomCover comes from an originallyGood candidate. Its Q belongs to goodAdvice and is contained in the leaf. Hence the zoom cover is contained in the union of the full upper cones of the distinct good Q. card_biUnion_le bounds this union by the sum of cone cardinalities; the pinned actual upperCount_eq computes each cone as gaussian(n-a,d-a). There is no attempted injection from multiple candidates to distinct Q.

For r<=d<=n, all relevant ambient Gaussian counts are positive. The pinned flag_product identity yields gaussian(n,a)*gaussian(n-a,d-a)=gaussian(n,d)*gaussian(d,a). Dividing, and multiplying by the actual number of distinct good Q, gives the exact incidence ratio. Summing proves mass(cover)<=sum_a goodAdviceFraction(a)*gaussian(d,a).

The final two theorems apply an explicit uniform numerical bound B on those actual gaussian(d,a) factors. Together with any actual strict cover-mass lower bound D, they give D/B<sum_a goodAdviceFraction(a). This B input is explicitly not yet discharged in this module. The successor must instantiate B=4*2^(d*d) from the concrete Gaussian theorem and D=originalDensity/(2m) from the finite-cover theorem, then specialize d=2h and average under the original complement law. The exact-budget pair is retained in each Q's membership. No random-history, source decoder or successful-complement conditioning is introduced.

Three project sources and four Mathlib source identities match the Full114 archive/manifest; the three new candidate dependencies are separately hash-pinned and uncompiled. Full114 was not accepted. Future GCP verification must rebind all dependencies to the accepted operator successor and retain every parent scope requirement. Eleven public theorem axiom requests and four definition checks are included. No local Lean/Lake execution occurred.

Remaining to-do list: concrete Gaussian specialization, cover/inverse/bad-mass integration and original-law dimension averaging; GCP kernel/axiom/warning verification; actual source decoder/NO, random-history, runtime and full certification.
'''
(OUT/'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, sha256=sha(raw), bytes=len(raw)))
manifest = dict(schema='numeric-distinct-advice-offer-v1', author='/root', story='E002/S3137',
    accepted=False, compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, external_dependencies=external, candidate_dependencies=candidate_deps,
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2', public_axiom_requests=exports,
    checked_definitions=definitions, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()),
    manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
