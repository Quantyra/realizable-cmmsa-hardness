from pathlib import Path
import hashlib
import json
import re

S = Path(__file__).resolve().parent
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
common = [
    ('numeric-refresh-history-offer-20261011-v6', 'ActualRefreshGaussian.lean', 'ActualRefreshGaussian', 'BF70B7ACA9E5874E01316BE5E3AD996C72C8FBB31CBE95D9CCF6A544B444CFD9'),
    ('numeric-refresh-history-offer-20261011-v6', 'ActualRefreshCandidateCount.lean', 'ActualRefreshCandidateCount', '15D10B8A1C1E3010CBB4411D86ACD961B85BFD4BA9C3D11B4BBC5BA592BBE4ED'),
    ('numeric-refresh-formal-offer-20261011-v1', 'ExactRefresh.lean', 'NumericRefreshFormalOffer', 'B68497790D514D4941E70E68F9AEF4D10493C572C9039058EB347C3963CD2BF3'),
    ('numeric-refresh-tail-offer-20261011-v2', 'ExactRefreshTail.lean', 'NumericRefreshTailOffer', '7B54EE1E137076B252C54C9268083412FE54C2FADC9705170FE4911400D4F538'),
    ('numeric-robust-real-offer-20261011-v2', 'ActualNumericRobustReal.lean', 'ActualNumericRobustReal', '3437068369905FDF688E52453245D6EC6E6ECAB1337D741153A618F081650CD7'),
    ('numeric-distinct-advice-offer-20261011-v1', 'ActualDistinctAdviceCoverage.lean', 'ActualDistinctAdviceCoverage', '2C9C6FA5C9847254D833CB084E7ACCE3F588FDFD7C7097B1BBDD3381FA6A9AB0')]
deps = []
for folder, file, module, pin in common:
    path = S/folder/file
    raw = path.read_bytes()
    assert sha(raw) == pin, str(path)
    deps.append(dict(path=str(path), module=module, bytes=len(raw), sha256=pin, status='uncompiled'))
argument = S/'numeric-refresh-argument-offer-20261011-v1/ARGUMENT.md'
argument_pin = '6C05AEBB2FCFE008EA6C7458367CDE24CA08C032A121A63AA7958589850B5DC7'
assert sha(argument.read_bytes()) == argument_pin
specs = [
    ('numeric-advice-average-offer-20261011-v1', 'ActualDistinctAdviceAverage', 6, 1, '''
The exact distinct-Q incidence argument was recorded before translation at planning50e29d8 and is implemented by ActualDistinctAdviceCoverage. For a<=r<=d, the concrete Gaussian upper bound is gaussian(d,a)<=4*2^(a*(d-a))<=4*2^(d*d). Applying it to the exact incidence sum proves sum_a goodAdviceFraction(a)>D/(4*2^(d*d)) from an actual cover-mass lower bound D. For d=2h and D=originalDensity/(2m), this is the manuscript density/(8*m*2^(4*h^2)) bound. The source explicitly invokes gaussian_upper_four; no Gaussian bound remains an input.

For any original FiniteLaw on a finite family of tables in the same coordinate ambient, the expectation retains ALL outcomes. If each member of a good set G has sum_a fraction>=D, multiply that inequality by its original nonnegative weight. Outside G, use the actual fraction's nonnegativity. Summing and exchanging the two finite sums gives sum_a E[fraction]>=mass(G)*D. Finite pigeonhole selects one a after averaging, with E[fraction(a)]>=mass(G)*D/(r+1). No normalization by mass(G) appears. Each good Q retains an exact-budget witness and therefore codimension r-a, so the selected dimension pair is fixed.

This module computes the actual Q fractions on the provided table family, but it still requires the caller to instantiate the actual complement law and coordinate-transported canonical tables, the good-complement mass and local cover bounds. Those inputs are handled by the complement-mass and selected robust assembly modules. The all-Q transverse correction, full H-extension loss and final source decoder are separate. All dependencies remain uncompiled, including the repaired v6 Gaussian source. The earlier known-invalid v4/v5 dependency bytes remain preserved and are not relabeled.
'''),
    ('numeric-refresh-preservation-offer-20261011-v1', 'ActualRefreshNumericPreservation', 4, 0, '''
The complete product-law/count/cutoff argument is already captured in the refresh ARGUMENT6C05A..., including the original selected numeric parameters. This module connects the actual uniform failure-mass theorem to the explicit Fn and eliminates an event-mass hypothesis.

With d=2h, write K=(2h-r)*(n-r-2h) and E=K+2-4h. The same guards h>=16,8(r+1)<=h,n>=8h+4r+16 imply K+2>=4h, so E+4h=K+2 in Nat. Taking powers of two gives 2^E*(2^(2h))^2=4*2^K. Therefore the actual Chernoff exponent -(2^(-2h))^2*2^K/3 equals -2^E/12 exactly. The v6 actual dependent-candidate count and actual-event union bound have prefactor16(r+1)^2*2^(n(r+1)), giving exactly refreshFailureBound h r n.

The previously captured numeric_refresh_total_failure_lt_half bounds the prescribed natural horizon times Fn by1/2 under the unchanged numeric floor. The horizon is at least1 and Fn is nonnegative, so Fn<1. The existing numeric dimension guards instantiate the generic actual mass bound for every finite X in the same V of dimension2*blocks A h. Thus the actual allCandidateFreshFailures mass is below1 for every X. exists_actual_preserving_refresh concludes existence of a fresh table outside that union; no favorable table or per-state bad-mass bound is supplied as a hypothesis.

This is a per-state existence theorem at the actual numeric parameters. It does not assert the random adaptive-history probability bound or construct the stopped random process. The exact arbitrary-table inverse still must be composed at the selected height to discharge the remaining finite-cover premise. The full same-table source decoder, runtime and all certification gates remain open.
''')]
prepared = []
for folder, module, expected_theorems, expected_defs, body in specs:
    out = S/folder
    assert not (out/'manifest.json').exists()
    raw = (out/(module+'.lean')).read_bytes()
    code = raw.decode('utf-8')
    assert not raw.startswith(b'\xef\xbb\xbf') and '\ufffd' not in code
    assert not re.search(r'\b(?:sorry|admit|axiom)\b', code)
    exports = re.findall(r'(?m)^theorem (\w+)', code)
    definitions = re.findall(r'(?m)^def (\w+)', code)
    assert len(exports) == expected_theorems, exports
    assert len(definitions) == expected_defs, definitions
    prepared.append((out, module, raw, exports, definitions, body))
for out, module, raw, exports, definitions, body in prepared:
    checks = 'import PvNP.RealizableHardness.'+module+'\n\n'
    checks += ''.join('#check PvNP.RealizableHardness.'+module+'.'+n+'\n' for n in definitions)
    checks += ''.join('#print axioms PvNP.RealizableHardness.'+module+'.'+n+'\n' for n in exports)
    (out/'Checks.lean').write_text(checks, encoding='utf-8', newline='\n')
    explanation = '# '+module+'\n\nE002/S3137. Uncompiled translation candidate.\n'+body
    explanation += '\nSix exact candidate dependency sources are hash-pinned. No local Lean/Lake, GCP or Git was invoked by this preparation. Future native execution must rebind the complete candidate closure to the accepted operator successor and retain all parent scope.\n\nRemaining to-do list: compose the original selected inverse and actual source laws; GCP kernel/axiom/warning verification; decoder/NO, random-history, runtime and full certification.\n'
    (out/'ARGUMENT.md').write_text(explanation, encoding='utf-8', newline='\n')
    (out/'.gitattributes').write_text('* -text\n', encoding='utf-8', newline='\n')
    files = []
    for path in sorted(out.iterdir()):
        content = path.read_bytes()
        assert not content.startswith(b'\xef\xbb\xbf') and '\ufffd' not in content.decode('utf-8')
        files.append(dict(path=path.name, bytes=len(content), sha256=sha(content)))
    manifest = dict(schema=out.name, author='/root', story='E002/S3137', accepted=False,
        compiler_invoked=False, candidate_dependencies=deps,
        complete_argument=dict(path=str(argument), sha256=argument_pin),
        mathlib_revision='e06eff5f95374108acfaf19f1ff7473aa7771df2',
        public_axiom_requests=exports, checked_definitions=definitions, files=files)
    (out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(json.dumps(dict(offer=out.name, source_sha256=sha(raw), checks_sha256=sha(checks.encode()),
        manifest_sha256=sha((out/'manifest.json').read_bytes()), exports=exports), indent=2))
