# S3132 r1006 exact API adjudication

Date: 2026-10-04 America/Los_Angeles. Model: GPT-6.1 Sol. Read-only; no Lean/Lake/elan, GCP, edits, Git writes, or subagents.

## Verdict

**GO-WITH-NOTES.** Luna correctly identified an absent composition theorem, but it can be stated in `ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean` with existing types and constants. No dependency source or mathematical premise needs to change.

`t2_right_derivative_expansion` reconstructs the entire complex function as a selector-filtered Fourier sum. The absent step identifies each complement's Fourier sum with an actual `typedW6FourierDerivative` on the common carrier; selector uniqueness alone is insufficient.

## Concrete first reconstruction

Open `ActualBinaryMatrixHC46T2Transfer`. The concrete statement is `a8_t2_actual_reconstruction`, parameterized by `Xmat`, `A2`, `B2`, the range/kernel inclusions, ambient base `T`, output shift `S`, complex input `g`, and common-carrier point `N`. Its left side is the affine restriction of the T2 hybrid filter of `actualW6Derivative Xmat T g`, transported back through
`(nestedCarrierEquiv (range X) A2 B2 (ker X) hA hB).symm N`.

Its right side sums over the existing
`a7T2ComplementPair X A2 B2`. For each complement `(C,H)`, set
`Z := t2QuotientRestrict C H X`; define the canonical quotient map
`qD : ((V/C)/range Z) -> V/A2` by quotient lifting; define
`qK : B2 -> ker Z` by restricting `a9AmbientBIncl B2 H`; and use the existing summand

```lean
typedW6FourierDerivative C H Z
  (filteredCarrierFunction C H
    (T + (ker X).subtype.comp (S.comp (range X).mkQ)) g)
  (qK.comp (N.comp qD))
```

All maps are canonical consequences of the complement conditions. The two carrier maps must be proved bijective downstream; this is a proof obligation, not a new premise.

## Proof route

1. Unfold `complexCarrierAffineRestrict` and apply `t2_right_derivative_expansion` at the affine argument.
2. Restrict the full pair sum to `a7T2ComplementPair` using `t2_left_to_right`, `t2_right_to_left`, and `t2_complement_unique`, following the complex analogue of `a7_left_mass_eq_complement_sum`.
3. For each complement, unfold `typedW6FourierDerivative`, `filteredCarrierFunction`, and `complexCarrierFourierCoeff`; use finite character orthogonality for the collision-fiber coefficient sum.
4. Match selectors and affine trace phases through `t2RightSelected`, `typedW6Precedes`, `qD`, and `qK`, proving complex-valued equality before norms.
5. Use `typedW6FourierDerivative_eq_actual` when converting each summand to actual W6 energy.

Specialize to `Xmat := a7MixedCoordinateParent t`, `T := 0`, and
`g := a7MixedCoordinate t T0 f`. Coordinate subspaces come from the existing output pair via domain/codomain bases. `manuscript_A1_complex`, the accepted coordinate helpers, and `a8_w6_domain_quotient_square` identify the endpoint with the exact `a9AmbientFinalMap` energy. Then use the energy-level two-stage Cauchy bound, `a7_t2_complement_card_le`, both base averages with `a7_base_translate_mean`, supported complementary vanishing, and `a7_pair_shares_exhaust`.

## Accounting

Accepted alone, `a8_t2_actual_reconstruction` would be helper-only increment 3. Proved and consumed inside `a8_output_q_le_actual_predecessor_sum`, it is manuscript-facing S3132 progress. The route decision authorizes only the integrated outcome; accepted helper count remains 2.

## Exactly one next action

Make one integrated authoring attempt in the owned A8 module that proves this reconstruction and consumes it through the averaged per-output-pair inequality into `a8_output_q_le_actual_predecessor_sum`.

