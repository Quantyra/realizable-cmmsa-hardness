# Accepted-good-mass inequality for starAcceptsCenter

Date: 2026-09-26. Theorem 1 and Corollary 2 are not claimed.
The increment is not route-final. Full CMMSA stays partial.
README.md and MANUSCRIPT.md are unchanged. No new carrier, palette,
or conditional wrapper is opened.

## Inequality

`Pr[starAcceptsCenter ∧ jointlyDirect] ≥ Pr[starAcceptsCenter] − r`
with `r < S/2`, where `S = 2^{-E}` and
`E = badExponent nRows (hBlock L nRows)`, at
`selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `2 * h`, center rank `leafT nRows h`,
and two leaves.

Lean theorem:
`selected_transverseStar_starAcceptsCenter_rankGood`.

## Same experiment

`starLaw` on `transverseComplement` of one question. `centerLaw` draws
the center. The two leaves are independent uniform extensions of that
center, presented as leaves of the question. `transverseStarAcceptsCenter` calls `starAcceptsCenter` on the presented
leaves of both extensions. `transverseStarAcceptsCenter_imp_equal` proves
acceptance implies those extensions are equal, so the event is contained
in the equal-extension event. Rank-good is `jointlyDirect` of the same
draw. The bad-star event is the negation of `jointlyDirect`.

The rank-good intersection is empty. The unconditional equal-extension
mass is `1 / gaussian(2 * J − t, leafK)`, and acceptance is at most that
mass. `selected_extensionCount_gt_halfMargin` proves the count is strictly
larger than `2^{E+1}`, so the acceptance mass is strictly below `S/2`.
The witness `r` is the acceptance mass. The fixed-star conditional
`2^{-4 (h − h / bOf nRows)}` is not this probability.

## Build

Local `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`.
