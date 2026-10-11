from pathlib import Path
import hashlib
import json
import re

S = Path(__file__).resolve().parent
OUT = S / 'numeric-refresh-cover-offer-20261011-v1'
sha = lambda b: hashlib.sha256(b).hexdigest().upper()
assert not (OUT/'manifest.json').exists()
dependencies = []
for folder, file, module, pin in [
    ('numeric-refresh-progress-offer-20261011-v1', 'ActualRefreshProgress.lean', 'ActualRefreshProgress', '52EB082615BEB23E1EC112045296686DFBA55DE42F0EC63E308AED4C33097DA2'),
    ('numeric-star-marginal-offer-20261011-v1', 'ActualOrdinaryStarLeafMarginal.lean', 'ActualOrdinaryStarLeafMarginal', '215B34D7EB1E71E33B1DAB0945BD12CF0A047FB957AD8011F09E8DA68D0BD5D2'),
    ('numeric-refresh-formal-offer-20261011-v1', 'ExactRefresh.lean', 'NumericRefreshFormalOffer', 'B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3'),
    ('numeric-refresh-tail-offer-20261011-v2', 'ExactRefreshTail.lean', 'NumericRefreshTailOffer', '7B54EE1E137076B252C54C9268083412FE54C2FADC9705170FE4911400D4F538')]:
    path = S/folder/file
    raw = path.read_bytes()
    assert sha(raw) == pin
    dependencies.append(dict(path=str(path), sha256=pin, module=module, bytes=len(raw), status='uncompiled'))
capture = S/'numeric-refresh-history-capture-v1'
index = json.loads((capture/'index.json').read_bytes())
source_row = next(r for r in index['files'] if r['copy'] == 'ActualRefreshCandidates.lean')
candidate = capture/source_row['copy']
assert sha(candidate.read_bytes()) == source_row['sha256']
dependencies.append(dict(path=str(candidate), sha256=source_row['sha256'], module='ActualRefreshCandidates', bytes=candidate.stat().st_size, status='uncompiled', capture_index_sha256=sha((capture/'index.json').read_bytes())))
source = (OUT/'ActualRefreshGoodCover.lean').read_bytes()
code = source.decode('utf-8')
assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
exports = re.findall(r'(?m)^theorem (\w+)', code)
definitions = re.findall(r'(?m)^def (\w+)', code)
assert len(exports) == 6
checks = 'import PvNP.RealizableHardness.ActualRefreshGoodCover\n\n'
checks += ''.join('#check PvNP.RealizableHardness.ActualRefreshGoodCover.'+n+'\n' for n in definitions)
checks += ''.join('#print axioms PvNP.RealizableHardness.ActualRefreshGoodCover.'+n+'\n' for n in exports)
(OUT/'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
argument = '''# One-refresh original-good zoom cover

E002/S3137. The complete finite-cover argument was recorded before translation in the planning numeric note, section 2026-10-11 One-refresh finite-cover argument for the robust existential. This candidate composes actual tables, actual failure events and actual decoded zooms. It is uncompiled.

For the fixed original T and e>0, an originallyGood candidate has the exact budget a+codim W=r and original agreement greater than e/2. Form X as the finite union of all such whole zooms in the complete Candidate carrier. The carrier and X are fixed before the fresh table is chosen. Every originallyGood candidate's zoom is contained in X.

From F outside the actual union of candidateFreshFailure events, each candidate's refreshed matching count in Zoom intersect X is at most 2p|Zoom|, p=2^(-d). If the intersection has size less than p|Zoom|, the count is at most its size. Otherwise, nonmembership in the strict-tail event gives count<=2p|intersection|<=2p|Zoom|. This also includes an empty zoom/intersection; no false positive lower count is required. The source proves this semantic bound from the actual event definition, rather than taking a favorable fresh table as a supplied premise.

The theorem takes a strict upper bound below one on the actual all-candidate bad-event mass for this particular X. exists_actual_preserving_refresh supplies F. Under 2p<=e/2, preservation feeds the exact progress theorem. If refreshed density were at least half the original, the arbitrary-table inverse premise would give an exact-budget nonempty zoom with agreement greater than e. Progress proves original agreement greater than e/2 and positive original matching count outside X. The resulting candidate belongs to the defining good family, hence its zoom is contained in X. The outside count is zero, contradicting positivity. Thus this F halves the density. The actual star-density variation theorem gives |X|/|Grass|>density(T)/(2m) for m>0.

The inverse premise retains the real project's Q/P/Zoom/agreement types and its original exact budget; candidateOfExactBudget injects that output into the already fixed finite carrier. It will be supplied by fixed_coordinate_real_inverse_agreement once the half-density lower bound S is verified for the chosen good complement. The actual event-mass premise will be supplied by the concrete Gaussian/candidate count and selected Fn cutoff. Both integrations are still required; this module does not claim a no-obligations numeric endpoint.

Distinct-Q coverage, dimension pigeonholing, complement/advice law, H-extension and source decoder are not proved here. The separate random-history BF_n statement remains open: this one-refresh existence proof does not assert it. All five candidate dependencies are exact-byte pinned and currently uncompiled; future execution must retain the complete parent scope and rebind to an accepted operator successor. No local Lean/Lake execution occurred.

Remaining to-do list: concrete numeric preservation and inverse instantiation, distinct-Q many-advice counting; GCP kernel/axiom/warning verification; source decoder/NO, history probability, runtime and complete certification.
'''
(OUT/'ARGUMENT.md').write_text(argument, encoding='utf-8', newline='\n')
(OUT/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
files = []
for path in sorted(OUT.iterdir()):
    raw = path.read_bytes()
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in raw.decode('utf-8')
    files.append(dict(path=path.name, sha256=sha(raw), bytes=len(raw)))
manifest = dict(schema='numeric-refresh-cover-offer-v1', story='E002/S3137', author='/root',
    accepted=False, compiler_invoked=False, dependencies=dependencies, public_axiom_requests=exports,
    checked_definitions=definitions, files=files, mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2')
(OUT/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(dict(source_sha256=sha(source), checks_sha256=sha(checks.encode()), manifest_sha256=sha((OUT/'manifest.json').read_bytes()), exports=exports), indent=2))
