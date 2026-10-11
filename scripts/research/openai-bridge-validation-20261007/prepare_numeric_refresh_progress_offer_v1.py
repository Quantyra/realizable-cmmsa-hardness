from pathlib import Path
import hashlib
import json
import re
import tarfile

S = Path(__file__).resolve().parent
OUT = S / 'numeric-refresh-progress-offer-20261011-v1'
ARCHIVE = Path(r'C:\Users\dfred\.quantyra\builder02\full114-exact-real-complex-operators-repair4-resource02\input-archive.tar.gz')
PIN = '70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'
REF = S / 'full107-trace-qualified-source-record-v1/review-sources'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT / 'manifest.json').exists()
assert sha(ARCHIVE.read_bytes()) == PIN
deps = []
with tarfile.open(ARCHIVE, 'r:gz') as archive:
    for name in ['ActualMaximalPairLadder', 'ActualSourceStarLaw', 'GrassmannCounting']:
        member = 'lean/PvNP/RealizableHardness/' + name + '.lean'
        raw = archive.extractfile(member).read()
        assert raw == (REF / member).read_bytes()
        deps.append(dict(member=member, bytes=len(raw), sha256=sha(raw)))
    parent = json.load(archive.extractfile('capture-manifest.json'))
external = REF / 'external/Mathlib/Data/Finset/Card.lean'
external_member = '.lake/packages/mathlib/Mathlib/Data/Finset/Card.lean'
assert sha(external.read_bytes()) == parent['cache_provenance']['package_sources'][external_member]
moment = S / 'numeric-refresh-formal-offer-20261011-v1/ExactRefresh.lean'
assert sha(moment.read_bytes()) == 'B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3'
source = (OUT / 'ActualRefreshProgress.lean').read_bytes()
code = source.decode('utf-8')
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 7, exports
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
checks = 'import PvNP.RealizableHardness.ActualRefreshProgress\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualRefreshProgress.' + n + '\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualRefreshProgress.' + n + '\n' for n in exports)
(OUT / 'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# Actual refreshed-table agreement and union progress

E002/S3137. Uncompiled translation of the Progress and termination step in the captured refresh argument, SHA 6C05AEBB2FCFE008EA6C7458367CDE24CA08C032A121A63AA7958589850B5DC7, already recorded in the planning numeric note before translation.

For the actual decoded Q,P, identify its Zoom subtype with the finite set of d-spaces containing Q and contained in P.W. Equality of a table label with targetFromMap is exactly AgreesOn; linear-map extensionality proves both directions. The equivalence restricts to AgreeingZoom. Thus the original rational agreement, cast to Real, equals the actual matching count divided by the zoom count whenever that count is nonzero. These are cardinal equalities for the real project types, not an assumed finite surrogate.

Refresh every entry in X from F and retain T outside X. Partition the agreeing entries of the selected zoom into its difference with X and its intersection with X. These two sets are disjoint, so the matching count is exactly the sum of original-table matches outside X and fresh-table matches inside X. This identity is pointwise even when Q,P were chosen after inspecting F.

If the original inverse theorem gives refreshed agreement greater than e, and preservation bounds the fresh matching count by (e/2)*|Zoom|, subtracting yields more than (e/2)*|Zoom| original matches outside X. Inclusion proves original agreement greater than e/2 on the same Q,P. The number of new entries is at least this outside matching count, while |X union Zoom|=|X|+|Zoom difference X|. This gives strict growth of the actual union by more than (e/2)*|Zoom|.

The endpoint still requires the actual inverse output and fresh-label preservation inequality. The latter follows from the separate all-candidate event using 2*2^(-d)<=e/2; it is not proved by this module. Normalized zoom lower bounds, the concrete transition, bounded stopping, uniform leaf marginal, density-change charge, deduplication and many-Q extraction remain explicit integration work. No theorem here assumes an arbitrary mass growth premise or calls an inconsistent all-active sequence a stopped history.

Dependencies are pinned to actual Full114 project members and the captured uncompiled moment source, routed as NumericRefreshFormalOffer. Full114 itself is unaccepted; native scope must bind to an accepted operator successor. All public theorem requests are included; no local Lean/Lake invocation occurred.

Remaining to-do list: actual Gaussian/candidate bounds and numeric preservation; inverse-driven history and many-Q integration; GCP kernel/axiom/warning verification and all source/decoder/runtime/certification gates.
'''
(OUT / 'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT / '.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, bytes=len(raw), sha256=sha(raw)))
manifest = dict(schema='numeric-refresh-progress-offer-v1', author='/root', story='E002/S3137',
    accepted=False, compiler_invoked=False, full114_archive=dict(path=str(ARCHIVE), sha256=PIN),
    dependencies=deps, candidate_dependency=dict(path=str(moment), sha256=sha(moment.read_bytes()), destination='NumericRefreshFormalOffer.lean'),
    external_dependency=dict(member=external_member, sha256=sha(external.read_bytes())),
    mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
    public_axiom_requests=exports, checked_definitions=definitions, files=files)
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()), manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
