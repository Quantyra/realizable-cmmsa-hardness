# Actual dependent Candidate cardinality — v5

Status: uncompiled Lean translation candidate for E002/S3137. This offer is disjoint from frozen v4 and preserves its Gaussian/Zoom source bytes. No compiler or kernel acceptance is claimed.

`ActualRefreshCandidateCount.lean` encodes the actual candidate

`Σ a : Fin (r+1), Σ Q : Grass V a.val, {P : DecodedPair Q d // a.val + codim P.W ≤ r}`

into a dependent finite union indexed by budgeted dimension pairs `(a,c)`. Each fiber stores an actual ambient `W` with `codim W=c`, an actual advice subtype `{Q // Q.val≤W}`, and an actual linear functional on `W`. The encoding sets `c=codim P.W` and retains `W`, `Q`, the containment witness, and `P.g`. The candidate budget supplies the pair membership and the `Fin (r+1)` bound. Equal encoded data recover `a,Q,W,g`; only the budget proof is omitted, and it is a proposition.

For a fixed `(a,c)`, the actual dual-annihilator injection gives `#W≤gaussian(n,c)`. At each W the advice spaces form an actual subtype of `Grass V a`, so their count is at most `gaussian(n,a)`. Finite-dimensional duality gives `#g=2^(n-c)`. The pinned Gaussian upper bound gives `#W≤4·2^(c*n)` and `#Q≤4·2^(a*n)`. Each W-fiber therefore has at most `4·2^(a*n)·2^(n-c)` members. Summing over W gives

`16·2^(c*n+a*n+n-c) ≤ 16·2^(n*(r+1))`.

The final theorem sums over the actual budget-pair subtype, whose cardinality is at most `(r+1)^2`, and proves

`Fintype.card (Candidate V d r) ≤ 16*(r+1)^2*2^(n*(r+1))`

from only `finrank V=n` and `r≤n`. It has no conditional cardinality premise and counts the actual dependent carrier.

The exact Gaussian bounds and actual Zoom cardinality/lower bound remain byte-for-byte from v4. This Lean source is uncompiled and requires Sol's GCP compile and axiom stages.
