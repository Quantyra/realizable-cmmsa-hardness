# Accepted-good-mass status

Date: 2026-09-26. The outcome-B stop in this file is withdrawn.
The inequality is `selected_presented_starAccepts_rankGood`.

`Pr[accept ∧ rankGood] ≥ Pr[accept] − q` with `q < S/2`,
`S = 2^{-E}`, `E = badExponent nRows (hBlock L nRows)`,
at `selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
leaf rank `2 * hBlock L nRows`, center rank `leafT nRows (hBlock L nRows)`.

The sample is `physicalPresentedLaw`. `physicalPresentedLaw_center` charges
the center by `centerLaw`. Acceptance is `starAccepts` on the presented
rank-`2h` leaves of that draw. Rank-good is `jointlyDirect` of that same star.

This is not Theorem 1, Corollary 2, or route-final. Full CMMSA stays partial.
No replacement carrier, palette, or conditional wrapper is opened.
