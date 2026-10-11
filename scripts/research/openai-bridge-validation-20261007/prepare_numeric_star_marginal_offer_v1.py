from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-star-marginal-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as f:
    for name in ['ActualSourceStarLaw', 'ActualChangedAmbient8SBoundary',
                 'GrassmannFlagPosterior', 'GrassmannCounting', 'ActualFiniteLaw']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = f.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, sha256=sha(raw), bytes=len(raw)))
    parent = json.load(f.extractfile('capture-manifest.json'))
external = []
for name in ['Mathlib/Logic/Equiv/Prod.lean', 'Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean', 'Mathlib/Data/Fintype/BigOperators.lean']:
    raw = (REF/'external'/name).read_bytes()
    member = '.lake/packages/mathlib/' + name
    assert sha(raw) == parent['cache_provenance']['package_sources'][member]
    external.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
source = (OUT/'ActualOrdinaryStarLeafMarginal.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
assert len(exports) == 6, exports
checks = 'import PvNP.RealizableHardness.ActualOrdinaryStarLeafMarginal\n\n'
checks += '#check PvNP.RealizableHardness.ActualOrdinaryStarLeafMarginal.ordinaryStarAverage\n'
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualOrdinaryStarLeafMarginal.'+n+'\n' for n in exports)
(OUT/'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# Ordinary star leaf marginal and actual density-change charge

E002/S3137. Translation of the complete leaf-marginal and density-drop argument already recorded in numeric-refresh-argument-offer-20261011-v1/ARGUMENT.md (SHA 6C05AEBB2FCFE008EA6C7458367CDE24CA08C032A121A63AA7958589850B5DC7) and the planning numeric note. Uncompiled candidate.

Fix actual binary V and t<=d<=dim(V). The ordinary experiment samples a uniform actual t-space K and then an ordered tuple of independent uniform actual d-spaces extending K. For any one occurrence i, split a function tuple into its ith value and all other values using Equiv.funSplitAt. Summing an arbitrary rational test function over this product cancels the cardinality of all other coordinates and leaves the uniform average on Extension K d. This is valid even if sampled leaves repeat; it does not assert independence of the unconditional leaves.

Every K has exactly E=gaussian(n-t,d-t) extensions. Interchange the finite sums over incident (K,L). For fixed L the lowerCount theorem gives M=gaussian(d,t) centers. The pinned flag_product identity gives gaussian(n,t)*E=gaussian(n,d)*M. Thus the occurrence average of every rational f(L) is exactly its uniform average on Grass V d. All canceled Gaussian counts are positive under the stated dimension inequalities.

ordinaryStarAverage writes this same ordered/common-center law as nested normalized finite sums. starDensity_eq_average identifies the actual StarDensity definition with the indicator average by unfolding only its uniform masses; it changes neither event nor conditioning. Applying the marginal theorem to the indicator of an arbitrary X gives |X|/|Grass V d| for every occurrence.

If T and T' agree outside X while the center table C stays fixed, acceptance for T without acceptance for T' implies some leaf occurrence lies in X. Otherwise all leaf restrictions are unchanged, which transports the full simultaneous acceptance event and contradicts rejection. Pointwise the old acceptance indicator is at most the new one plus the sum of the m occurrence indicators. Monotonicity, linearity and the exact marginal give density(T)<=density(T')+m*|X|/|Grass|. Swapping the tables proves the absolute-difference bound. If the new density is strictly below half the old density and m>0, elementary rearrangement proves |X|/|Grass|>density(T)/(2m).

This proves the actual density-change charge used after a stopped refresh history; it does not construct that history or its many-Q witnesses. The zero-occurrence case is retained in the variation theorem (the sum is zero); only the final division by 2m assumes m>0. Actual source outer-question conditioning, H-extension/advice correction, source decoding/NO, runtime and full certification remain separate obligations.

Five project dependencies and three exact Mathlib source identities were verified against the actual Full114 input manifest. Full114 is unaccepted, so a future native package must rebind to the accepted operator successor. Six public theorem axiom requests and the expectation-definition check are included. No Lean/Lake was invoked locally.

Remaining to-do list: GCP kernel/axiom/warning verification; concrete refresh counting, inverse-driven stopped history and distinct-Q extraction; actual source/decoder/runtime and all remaining certification gates.
'''
(OUT/'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for p in sorted(OUT.iterdir()):
    raw = p.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=p.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema='numeric-star-marginal-offer-v1', author='/root', story='E002/S3137',
    accepted=False, compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, external_dependencies=external, mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, files=files)
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()), manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
