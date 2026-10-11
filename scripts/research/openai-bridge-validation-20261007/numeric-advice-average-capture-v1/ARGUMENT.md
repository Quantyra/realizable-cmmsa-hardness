# ActualDistinctAdviceAverage

E002/S3137. Uncompiled translation candidate.

The exact distinct-Q incidence argument was recorded before translation at planning50e29d8 and is implemented by ActualDistinctAdviceCoverage. For a<=r<=d, the concrete Gaussian upper bound is gaussian(d,a)<=4*2^(a*(d-a))<=4*2^(d*d). Applying it to the exact incidence sum proves sum_a goodAdviceFraction(a)>D/(4*2^(d*d)) from an actual cover-mass lower bound D. For d=2h and D=originalDensity/(2m), this is the manuscript density/(8*m*2^(4*h^2)) bound. The source explicitly invokes gaussian_upper_four; no Gaussian bound remains an input.

For any original FiniteLaw on a finite family of tables in the same coordinate ambient, the expectation retains ALL outcomes. If each member of a good set G has sum_a fraction>=D, multiply that inequality by its original nonnegative weight. Outside G, use the actual fraction's nonnegativity. Summing and exchanging the two finite sums gives sum_a E[fraction]>=mass(G)*D. Finite pigeonhole selects one a after averaging, with E[fraction(a)]>=mass(G)*D/(r+1). No normalization by mass(G) appears. Each good Q retains an exact-budget witness and therefore codimension r-a, so the selected dimension pair is fixed.

This module computes the actual Q fractions on the provided table family, but it still requires the caller to instantiate the actual complement law and coordinate-transported canonical tables, the good-complement mass and local cover bounds. Those inputs are handled by the complement-mass and selected robust assembly modules. The all-Q transverse correction, full H-extension loss and final source decoder are separate. All dependencies remain uncompiled, including the repaired v6 Gaussian source. The earlier known-invalid v4/v5 dependency bytes remain preserved and are not relabeled.

Six exact candidate dependency sources are hash-pinned. No local Lean/Lake, GCP or Git was invoked by this preparation. Future native execution must rebind the complete candidate closure to the accepted operator successor and retain all parent scope.

Remaining to-do list: compose the original selected inverse and actual source laws; GCP kernel/axiom/warning verification; decoder/NO, random-history, runtime and full certification.
