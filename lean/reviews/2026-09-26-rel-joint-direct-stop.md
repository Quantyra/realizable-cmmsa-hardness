# Stop: same-question Rel and joint directness

Date: 2026-09-26. Theorem 1 and Corollary 2 are not claimed.
The increment is not route-final. Full CMMSA stays partial.
README.md and MANUSCRIPT.md are unchanged. No new encoder, palette,
or conditional wrapper is opened. No GCP replay is attached.

## Frozen sample

One question at
`selector (fun n => max (sourceHMin n) (n + 2)) L = nRows`,
`h = hBlock L nRows`, leaf rank `2 * h`, center rank `leafT nRows h`,
and two leaves.

1. `centerLaw` draws the center inside `transverseComplement`.
2. The two leaves are independent uniform extensions of that center.
3. Labels may be drawn afterwards.
4. Acceptance is `starAcceptsCenter` of those presented leaves.
5. Rank-good is `jointlyDirect` of that same `StarTuple`.

## Stop

No draw meets both predicates. `starAcceptsCenter` is stated only with
`LeafVertex.Rel`. On one question that relation is equal domains
(`leafVertex_rel_sameH_iff_domain`, `vertexOfGrass_H`). Equal domains of
the two presented extensions are the same extension
(`vertexOfGrass_eq_of_domain`). Two equal extensions are not
`jointlyDirect` (`equalPair_not_jointlyDirect`) once
`leafT < 2 * h`, which the selector gives.

Lean theorem: `selector_starAcceptsCenter_not_jointlyDirect`.
Same-question `Rel` and joint directness are incompatible at two leaves.

The positive-mass form
`Pr[starAcceptsCenter ∧ jointlyDirect] ≥ Pr[starAcceptsCenter] − q`
with `q < S/2` and `Pr[starAcceptsCenter ∧ jointlyDirect] > 0`
has empty intersection, so it is not available. `q := Pr[accept]` is
not used.

`selected_extensionCount_gt_halfMargin` remains a collision bound.
It does not put positive mass on stars that are both accepted and
rank-good.

## Review

Local `lake build PvNP.RealizableHardness.ActualStarAcceptedGoodMassChecks`
exited 0 (3272 jobs). Axioms of
`selector_starAcceptsCenter_not_jointlyDirect`: `propext`,
`Classical.choice`, `Quot.sound`.

Proof-adversarial: GO. `Rel` forces the two extensions to coincide, and
equal extensions fail `jointlyDirect` at two leaves. No GCP replay: the
surviving statement is this stop, not a positive-mass producer.
