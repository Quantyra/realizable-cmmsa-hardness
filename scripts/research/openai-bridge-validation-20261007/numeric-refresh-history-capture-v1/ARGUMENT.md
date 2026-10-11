# Actual all-candidate refresh law

Status: uncompiled source candidate for E002/S3137, continuing the captured actual dual-label tail. `ActualRefreshCandidates.lean` defines the finite manuscript candidate universe `(a,Q,P)` with `a+codim(W)≤r`, the actual distinct `d`-spaces in `X∩Zoom(Q,P)`, and the target table induced by `P.g`. It proves each candidate's actual product-law tail and sums over the entire candidate universe before any table-dependent inverse choice.

For a fixed `X`, candidates with fewer than `p` times the zoom size in `X` have no failure event: their refreshed agreement contribution is deterministically below `p`. For every other candidate, the fresh failure event is the strict event

```text
Y_(Q,W,g) > 2p |X ∩ Zoom(Q,W)|,  p=2^-d.
```

The captured actual tail theorem gives its probability at most
`exp(-p |X∩Zoom|/3)`. `allCandidateFreshFailures_mass_bound` bounds the mass of the union by the sum of these candidate-specific tails. This statement uses the full finite carrier of advice spaces, decoded spaces, and functionals, including candidates with `a+codim(W)<r`; it does not choose an inverse output before the table, or condition on a successful candidate.

`exists_actual_preserving_refresh` extracts a fresh table outside the complete union when the actual union mass is below one. This is the positive-mass argument needed at each fixed state. It does not treat a favorable table as an input premise.

## Remaining translation to the manuscript one-step bound

The sum still has candidate-specific `|X∩Zoom|`. To recover the manuscript `F_n`, use the actual Gaussian zoom count and ambient count to show, on every candidate retained by the large-intersection test,

```text
|X∩Zoom| ≥ 2^-d · 2^((d-r)(n-r-d)),
p|X∩Zoom| ≥ 2^E/4,
E = -4h + 2 + (2h-r)(n-r-2h), d=2h.
```

Then count the finite candidates by dimensions `a,c≤r`, subspaces, and functionals. Gaussian upper counts give at most `4·2^{a(n-a)}` advice spaces, `4·2^{c(n-c)}` choices of `W`, and `2^{n-c}` functionals on each `W`; there are at most `(r+1)^2` dimension pairs with `a+c≤r`. This is at most `16(r+1)^2 2^{n(r+1)}`. The captured Real cutoff supplies `F_n<1`. These Gaussian lower/upper estimates and the concrete candidate-cardinality estimate have not been added to this source.

## Remaining successful history and many-Q proof

With `F_n<1` uniformly at every state, use `exists_actual_preserving_refresh` recursively. Refresh all of `X`; preserve the original table outside `X`. If density is at least half its initial value, apply the fixed-coordinate inverse to the refreshed table and add the entire returned zoom to `X`; otherwise absorb the process. A preserving table limits its refreshed-coordinate contribution to `2p`, so each successful inverse step adds more than `e/2` original-table agreement. The zoom mass is at least `2^-rn/4`, giving growth more than `e·2^-rn/8`. The horizon `ceil(8·2^(rn)/e)+1` cannot contain only active steps because `μ(X)≤1`; hence it ends below half density.

The source has not yet encoded this concrete stopping recursion, the fixed-coordinate inverse interface, or the acceptance-change and incidence argument. It also does not prove the separate random-history event bound `B_n F_n`; a finite-choice history proves existence only. Distinct-Q deduplication, Gaussian force count, and averaging over the full unconditioned complement law remain open, followed by the original source decoding and certification obligations.
