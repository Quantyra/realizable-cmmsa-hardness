# Fixed-functional exact-budget matrix-lift review

Satellite commit `a7823d0` closes a bounded premise bridge in the NO path.
For each **fixed** leaf table `T` and ambient functional `f`, before any zoom
is chosen, `ActualFixedFunctionalMatrixLift.failed_zoom_gives_exact_bound`
assumes that **every nonempty exact-`r` zoom** has agreement at most `e` for
every decoded pair. It identifies the matching-leaf indicator on a zoom with
the agreeing-leaf count for the pair `(W, f|W)`, yielding
`ExactBudgetZoomBound r d (grassIndicator (matchingLeafSet T f)) e`.

`failed_zoom_gives_nominal_pseudorandom` consumes the finite matrix lift
proved in `2bac70b` and, under `r<d` and `e>=0`, yields
`PseudorandomExact r (2*e) (rankImageBoolean (matchingLeafSet T f))` over
**every nonempty raw nominal-budget-`r` fibre**. The factor two is the
matrix-lift loss; the matching-count identity has no further loss. These
quantifiers and constants agree with the matrix-lift and inverse setup in
`paper/body.tex`, Lemmas `matrix-lift` and `inverse-explicit`.

| Review lens | Bounded bridge | All-ambient inverse, robust `8S`, core Theorem 1 |
| --- | --- | --- |
| Proof adversarial | GO-WITH-NOTES | INCOMPLETE |
| Complexity theory | GO-WITH-NOTES | INCOMPLETE |
| Non-claims boundary | GO-WITH-NOTES | INCOMPLETE |

This is a fixed-`T,f` conditional implication. It does not select the global
`f`, prove the tagged complement law, discharge the all-ambient inverse
inequality, or derive the changed-ambient `8S` conclusion. The numerical
NO-soundness gap is unchanged.
