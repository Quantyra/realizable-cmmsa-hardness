# Ledger-selected parameter certificate: bounded review

`ActualLedgerSelectedParameters.lean` supplies a separate conditional
parameter family without changing the production family's placeholder
`manuscriptSourceFloor m = m+2`. The family selects the maximum admissible
`m(L)` against a fixed `SourceHeightBounds` ledger. Lean proves eventual
population, unbounded selected `m`, ledger readiness, the exact `/16`, `/4`,
`/2` sigma budget, a four-label budget, fixed-rho amplification margin,
`gamma_L → 0`, and `log σ_L/log L → 1` in the quantified rational lower-bound
form `∀ k>0, ∃ L₀, ∀ L≥L₀, 1-1/k ≤ log₂σ_L/log₂L`.

The wrapper `exists_outer_scale_and_ledger_selected_parameters` fixes
arbitrary `κ : ℝ` with `κ>0`, chooses an actual integer `A` with `20<κA`,
then takes a ledger supplied for that `(κ,A)` and proves eventual selection
at all sufficiently large input lengths. `τ` is intentionally absent: this
module has no `τ`-dependent conclusion; the manuscript's positive YES error
is chosen only after the fixed block and decoder parameters in the core
reduction. The wrapper's ledger provider supplies numeric heights, not a
proof that any cited or manuscript comparison works at those heights.

The seven source-height sufficiency obligations remain **external**:
`inverse`, `robustHistory`, `covering`, `posterior`, `maximalCount`,
`outerDecoder`, and `compilation`. None is discharged by taking their finite
maximum. The arbitrary-fixed-table representative-selection comparison,
changed-ambient `8S` application, encoded YES/NO maps, and Theorem 1
composition remain open. This parameter result reduces **no numeric
NO-soundness gap**.

## Verification and review

`lake build PvNP.RealizableHardness.ActualLedgerSelectedParameters
PvNP.RealizableHardness.ActualLedgerSelectedParametersChecks` passed with
3,266 jobs before the order wrapper; the post-wrapper targeted build also
passed with 3,435 jobs. The checks print the theorem statements and axioms.
The only axioms reported for the listed results and wrapper are `propext`,
`Classical.choice`, and `Quot.sound`.

| Lens | Bounded parameter family | Core Theorem 1 |
| --- | --- | --- |
| Proof-adversarial | GO-WITH-NOTES | NO-GO |
| Complexity theory | GO-WITH-NOTES; κ→A→ledger→L wrapper added after the review request | NO-GO |
| Non-claims boundary | GO-WITH-NOTES; external cutoff sufficiency and absent τ-dependent claim are explicit | NO-GO |

The three-lens table is a bounded-increment review record, not a core
certificate or route-final closeout. Planning review debt S3126 remains open.
