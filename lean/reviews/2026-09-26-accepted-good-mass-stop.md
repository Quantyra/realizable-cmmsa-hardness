# Accepted-good-mass inequality on the joint source law

Date: 2026-09-26. The earlier failure claim stays withdrawn. This note
records the inequality that is now proved. Theorem 1 and Corollary 2 are
not claimed. The increment is not route-final. Full CMMSA stays partial.
No replacement carrier, palette, or conditional wrapper is opened.
README.md and MANUSCRIPT.md are unchanged.

## Inequality

`Pr[equalLeaf ∧ jointlyDirect] ≥ Pr[equalLeaf] − r` with `r < S/2`,
where `S = 2^{-E}` and `E = badExponent nRows (hBlock L nRows)`,
at `selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `d = 2 * h`, center rank
`t = leafT nRows h`, and `r = 2`.

Lean theorem:
`selected_transverseStar_equalLeaf_accepted_rankGood`
in `lean/PvNP/RealizableHardness/ActualStarAcceptedGoodMass.lean`.

## Sample space

For a question center whose block count is `blocks A h` and whose center
rank is `leafT`, the ambient is `transverseComplement`: a complement of
the equation span inside the question coordinate space.
`transverseComplement_finrank` gives dimension `2 * blocks A h`.

`starLaw` on that complement draws the center from `centerLaw`, then two
independent uniform extensions of rank `2 * h`. `jointlyDirect` is the
bad-star event of that same draw. The sampled center is not the question's
stored subspace.

## Accept event

The event in the mass theorem is equal extensions: the two leaves are the
same subspace. It is not `starAcceptsCenter`. `jointlyDirect` is rank-good,
not the bad-star event. The bad-star event of the same draw is the negation
of `jointlyDirect`.

`starLaw_equalPair_mass` gives the unconditional equal-extension mass
`1 / gaussian(2 * J − t, leafK)`. `equalPair_not_jointlyDirect` shows the
intersection with rank-good is empty, so the inequality is witnessed by
`r` equal to that mass. `selected_extensionCount_gt_halfMargin` shows the
Gaussian count is strictly larger than `2^{E+1}`, so the mass is strictly
below `S/2`.

`leafVertex_rel_sameH_iff_domain` says same-question `LeafVertex.Rel` is
equal domains. That lemma is not the mass event. The fixed-star conditional
`2^{-4 (h − h / bOf nRows)}` is not this probability.

Proof-adversarial and complexity reviews are NO-GO for treating this as the
`starAcceptsCenter` inequality. See
`lean/reviews/2026-09-26-accepted-good-mass-three-lens.md`.
GCP replay debt: `gcp-replay-equal-leaf-inequality-2026-09-26`.

## Build

Local `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Axioms of the theorem: `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`.
