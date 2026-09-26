# Stop: same-experiment accepted-good mass

Date: 2026-09-26. Outcome B. Theorem 1 and Corollary 2 are not claimed.
No replacement carrier, palette, or conditional wrapper is opened.

## Failed inequality

`Pr[accept ∧ rankGood] ≥ Pr[accept] − q` with `q < S/2`,
where `S = 2^{-E}` and `E = badExponent nRows (hBlock L nRows)`,
at `selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
with `h = hBlock L nRows`, leaf rank `2 * h`, center rank `leafT nRows h`,
and `blocks` at that height.

The sample must draw its center from `centerLaw` and its leaves from the
manuscript `PresentedLeaf` rank-`2h` law. Acceptance must be that law's
physical label-agreement event. Rank-good must be the bad-star event of
those same leaves.

## Kill

`starAccepts` and `starAcceptsCenter` are that physical acceptance event:
transported `LeafLabel`s agree on the shared center by
`restrictionAgreesOnCenter`. No `FiniteLaw` has carrier `PresentedLeaf`
or `LeafVertex`.

`selected_transverseLeaf_accepted_rankGood` measures `starLaw` on
`Extension` tuples inside `transverseComplement`. `transverseLeafAccept_holds`
proves that geometric predicate for every sample, and the proof sets the
acceptance event equal to `Finset.univ`, so its mass is 1. The inequality
proved there is a `jointlyDirect` bound. `presentedOfTransverseLeaf` is not
the sample space.

That fails the kill test that acceptance is `starAccepts` on the
`PresentedLeaf` leaf law of the same center draw. Stop.
