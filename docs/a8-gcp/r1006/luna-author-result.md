# S3132 r1006 Luna resumed author result

Date: 2026-10-04 America/Los_Angeles

## Result: integrated attempt stopped before Lean edits

I read `exact-api-adjudication.md` completely and traced its proposed reconstruction against the existing declarations. No theorem was added to either owned Lean file, so there are no partial Lean edits to revert. The integrated endpoint is not authored and no helper-only increment is claimed.

The adjudication correctly identifies a potentially useful route, including `t2_right_derivative_expansion`, `a7T2ComplementPair`, `t1FilteredCarrierFunction_fourierCoeff`, and `typedW6FourierDerivative_eq_actual`. The decisive per-complement calculation is still a substantial equality proof. I could not establish it faithfully from the API statements without Lean elaboration, and the task prohibits compiler use. In particular, I cannot responsibly claim a whole-function reconstruction theorem based on a schematic route.

## Exact first proof obligation that failed

The first unproved obligation is the per-complement summand identity needed after reindexing the frequency sum in `t2_right_derivative_expansion`. With existing names and types, for

```lean
Xlin := Xmat.transpose.toLin'
R := LinearMap.range Xlin
K := LinearMap.ker Xlin
Z := t2QuotientRestrict C H Xlin
```

and a complement `p : a7T2ComplementPair Xlin A2 B2`, the attempted reconstruction needs to prove the actual complex-valued equality

```lean
∑ Y : BinaryMatrix n d,
  if t2RightSelected Xlin Y.transpose.toLin' A2 B2 p.1.1 p.1.2 then
    complexFourierCoeff g Y *
      (traceCharacter Y.transpose.toLin'
        (T + K.subtype.comp (S.comp R.mkQ) +
          K.subtype.comp (N.comp R.mkQ)) : Complex)
  else 0
  =
typedW6FourierDerivative C H Z
  (filteredCarrierFunction C H
    (T + K.subtype.comp (S.comp R.mkQ)) g)
  (qK.comp (N.comp qD))
```

where `qD : ((V d ⧸ C) ⧸ LinearMap.range Z) →ₗ[F] V d ⧸ A2` is the canonical quotient-lift map and `qK : B2 →ₗ[F] LinearMap.ker Z` is the restriction of `a9AmbientBIncl B2 H`. The target equality must also discharge the selector equivalence between `t2RightSelected Xlin ... p.1.1 p.1.2` and `typedW6Precedes C H Z Z'`, and the phase equality induced by `qD`, `qK`, and the common-carrier reindexing.

The currently available `t1FilteredCarrierFunction_fourierCoeff` has a different concrete boundary: it expands
`complexCarrierFourierCoeff C H (filteredCarrierFunction C H T g) Z'`
as a fiber over the restriction
`C.mkQ.comp (Y.transpose.toLin'.comp H.subtype)`. It does not directly give the displayed complement-indexed coefficient identity. Bridging these requires proving the carrier-frequency correspondence, selector equivalence, and phase compatibility for every complement. Those are precisely the steps needed before invoking `typedW6FourierDerivative_eq_actual`; the theorem only converts the already-identified typed derivative and cannot prove this identity. I did not infer these equalities from selector uniqueness alone.

Since that complex equality is the first input to `a8_t2_actual_reconstruction`, no faithful `N^3` estimate, corrected complement-count application, both-base averaging, supported-window discharge, all-pair summation, or exact A9 endpoint follows in this attempt. No termwise squared-energy equality or alternate pointwise-in-`T` claim is asserted.

## Smallest next proof work

Within the authorized A8 module, first prove the explicit complement-side equality above by constructing and checking the canonical quotient/kernel carrier equivalences and proving selector and phase compatibility using `t2_right_to_left`, `t2_complement_unique`, `t1FilteredCarrierFunction_fourierCoeff`, and the existing typed Fourier conversion. Then the concrete reconstruction can be assembled from `t2_right_derivative_expansion`. The integrated S3132 endpoint still must be proved in the same accepted authoring increment; the reconstruction alone is not helper-count progress under the current accounting instruction.

## Changed paths and execution

Changed path: `docs/a8-gcp/r1006/luna-author-result.md` only. The two owned Lean source/check paths remain unchanged.

No Lean/Lake/elan/compiler, GCP, Git write, formatter, destructive command, or subagent was used. Accepted helper count remains 2; no authoring increment is claimed.
