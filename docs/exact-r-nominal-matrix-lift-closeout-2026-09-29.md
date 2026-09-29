# Exact-r nominal matrix-lift: bounded closeout

Commit `2bac70b` proves `exact_zoom_implies_nominal_pseudorandom` in
`MatrixLiftNominalDirectComparison.lean`. For `r < d`, `e ≥ 0`, and an
arbitrary Boolean target on the (d)-Grassmannian, the premise
`ExactBudgetZoomBound r d (grassIndicator g) e` covers every nonempty zoom
with lower dimension plus upper codimension **exactly** `r`. The conclusion
`PseudorandomExact r (2*e) (rankImageBoolean g)` covers every raw nominal
matrix restriction with budget exactly `r` and a nonempty fibre.

The proof selects an arbitrary matrix in that fibre as its anchor. If the
anchor's prescribed fixed columns are dependent, every matrix in the same
fibre is rank deficient, so its rank-image density is zero. Otherwise, the
proof transports the raw target fibre through the residual zero-kernel
normal form, uses the strict binary full-rank target count to bound its
average by twice the free average, and applies the exact-budget zoom bound.
The fibre-cardinality transport uses `Fintype.card`/`Nat.card` equivalences;
the proof establishes positive denominators before division. Basis choices
occur internally, but a separate basis-invariance theorem is not exported.

| Lens | Review | Boundary |
| --- | --- | --- |
| Proof-adversarial | GO-WITH-NOTES | The exact-r quantifiers, arbitrary nonempty raw fibre, dependent-zero branch, and direct factor-two count are proved. No new `sorry` or axiom declaration appears in the committed files; the Checks module prints the theorem's axiom dependencies. |
| Complexity-theory | GO-WITH-NOTES | This is a finite matrix-distribution comparison. It does not construct an encoded reduction or establish runtime. |
| Non-claims boundary | GO-WITH-NOTES for this bounded theorem; NO-GO/INCOMPLETE for 8S and core | The theorem is not yet applied to the actual tagged side test or an all-ambient inverse. The numeric NO-soundness gap is unchanged. |

This is force-comparison evidence, not route-final certification of the
changed-ambient 8S application or CMMSA Theorem 1. Those applications need
their own typed transport and closeout.
