# Proof-adversarial review: partition 2/9 (Full89, original A22/HC46/selected-consumer milestone)

**Verdict for this partition: GO-WITH-NOTES.** This covers only the 18 files supplied here. It is not a verdict on the whole campaign or on the full A22/HC46 consumer.

## Scope and method

- I read every supplied file body in full and skipped none.
- I used no tools, no writes and no subagents. Lean was not run.
- Compile status, the axiom profiles and the 0 unresolved trace nodes come from the scope statement you supplied. I did not reproduce them.
- References are by declaration name. I did not compute line numbers, because counting them without tools would be unreliable.

## File status

| # | File | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A18OriginalGlobalInduction.lean | Inspected |
| 2 | ActualBinaryMatrixHC46A18QuotientSamplingLaw.lean | Inspected |
| 3 | ActualBinaryMatrixHC46A18SourceConditioning.lean | Inspected |
| 4 | ActualBinaryMatrixHC46A18SourceGlobal.lean | Inspected |
| 5 | ActualBinaryMatrixHC46A18TransposeAverage.lean | Inspected |
| 6 | ActualBinaryMatrixHC46A18TransposeTransport.lean | Inspected |
| 7 | ActualBinaryMatrixHC46A20SquareGlobalness.lean | Inspected |
| 8 | ActualBinaryMatrixHC46A20SquareSupport.lean | Inspected |
| 9 | ActualBinaryMatrixHC46A21DyadicMoment.lean | Inspected |
| 10 | ActualBinaryMatrixHC46A22OperatorLq.lean | Inspected |
| 11 | ActualBinaryMatrixHC46A22OperatorLqChecks.lean | Inspected (harness only) |
| 12 | ActualBinaryMatrixHC46A22OriginalInductionChecks.lean | Inspected (harness only) |
| 13 | ActualBinaryMatrixHC46A22ParentFactorizationChecks.lean | Inspected (harness only) |
| 14 | ActualBinaryMatrixHC46A6Transfer.lean | Inspected |
| 15 | ActualBinaryMatrixHC46A7CarrierParseval.lean | Inspected |
| 16 | ActualBinaryMatrixHC46A7EnergyConsumer.lean | Inspected |
| 17 | ActualBinaryMatrixHC46A7HybridW6Transport.lean | Inspected |
| 18 | ActualBinaryMatrixHC46A7PredecessorCount.lean | Inspected |

## What checks out

**Quantifiers, assumptions and vacuity**
- **Influence premise (`OriginalActualInfluenceThrough`).** It is a full uniform carrier mean, for every A, B and linear T with rank cost ≤ D. It is not a conditional fibre mean.
  - The order-zero seed (⊥, ⊤, T = 0) gives the ambient energy (`original_influence_order_zero_seed_ambient`).
  - The premise is not vacuous: f = 0 with eps = 0 satisfies it.
  - In A20 the premise is produced from globalness via the A16 bound (`a20_three_degree_global`), not assumed.
- **Unrestricted eta.** No theorem in A18, A20, A21 or A22OperatorLq assumes `0 ≤ eps`. Nonnegativity is always derived from the premises:
  - `original_influence_parameter_nonneg`
  - `actual_source_parameter_nonneg`
  - `filteredCarrierFunction_parameter_nonneg`
  - `UpToActualLqGlobal_parameter_nonneg`

  The degree-zero, r = 0 and zero-parameter cases are handled explicitly. None of these signatures contains an added hHC-style premise.

**`actual_A18_original_global` (the A18 induction)**
- It uses strong induction on D, generalizing n, d, r, eps and f, with an inner strong induction on r. Its only hypotheses are support D and influence D.
- Proof direction:
  - The top layer uses the IH at (D, r−1) and, for cost-one derivatives, at (D−1, r−1).
  - Lower layers i < D use the IH at (i, r).
  - The non-exact-order branch uses the IH at r−1 plus monotonicity of the budget.
  - The order-one derivative transfer (`original_influence_order_one_derivativeCoordinate_reduction`) keeps eps unchanged and uses exact additive endpoint cost (`relative_endpoint_cost_add`).
- Numerical bounds, recomputed independently, taking `a18BudgetScale D r eps = 2^(10Dr)·eps` from how the proof unfolds it:
  - Top contribution: `2·2^(10(D−1)(r−1)) + 4·2^(2D)·2^(10D(r−1))` is at most (1/512 + 8/512) times the budget for D, r ≥ 1, so 9/512 holds. 9/512 ≤ 1/4 then gives `htopHalf`.
  - Lower contribution: `2(Σ_{i<D} 2^(5ir))²·eps ≤ ~2.13·2^(−10r)·budget`, which is at most budget/2. So the external `a18_lower_absorption` lemma is numerically plausible.

**A20 and A21 exponents** (recomputed)
- A20: 10·D·3D + 11D² = 41D². Then 114 + 41 + 41 = 196, giving `2^(196D²)·eps²` (`manuscript_A20_raw_fourth_le`, `manuscript_A20_actual`).
- A21 exponent recurrence: 4(200q² − 100q) + 196(q/2 − 1) + 114 ≤ 800q² − 200q. This reduces to 98q − 82 ≤ 200q, which holds.
- A21 power of eps: 1 + 2(q/2 − 1) = (2q)/2 − 1.
- A21 base cases: p = 2 needs a(2) = 600 ≥ 0, and p = 4 needs a(4) = 2800 ≥ 114. Both hold.
- The IH in `a21_dyadic_strong` quantifies over all n, d, D, eps and f, so applying it to f² at degree 2D is legitimate.

**A22OperatorLq**
- q is real with only `1 ≤ q`, which Minkowski needs.
- The loss coefficient is `(1+2^(k+1))(1+2^k)`.
- `a22_A14_coefficient_le` bounds this by 2^(3j): it gives 2^(2j+1), and 2j + 1 ≤ 3j exactly when j ≥ 1, which is assumed.
- The hyperplane case goes through the transpose.

**Source conditioning** (files 3–4)
- `outsideColumn_card_half` holds: the outside-column event has exactly half the mass, because |B'| = 2|B|.
- Conditional mean ≤ 2 × full mean, correctly oriented for nonnegative statistics.
- `stableSourceCoordinatesEquiv` is a genuine bijection; the inverse I checked is `(N, λ) ↦ (N v, N∘s − λ⊗N v, λ)`.
- In `stable_expanded_source_mixture_le_two`, the step (η + 2η)/2 ≤ 2η uses the derived `η ≥ 0`.
- Jensen (`normSq_iterated_average_le`) is applied in the correct direction.

**A6 and A7**
- `a6_exponent_le` holds: 7D(i+j) + 3ij ≤ 10D(i+j) ≤ 20Dt ≤ 24Dt.
- The Gaussian-binomial count is ≤ 4·2^(k(j−k)): the diagonal frame product is ≥ 1/4.
- `w6_weighted_rank_term_le`: 2k(j−k) + 4k(D−k) + 6k ≤ 6Dk for k ≥ 1.
- Total predecessor weight: 1 + 4/63 = 67/63 ≤ 2.

## Findings

| ID | Severity | Location | Finding |
|---|---|---|---|
| F1 | Integration | `actual_A18_original_global` | Soundness depends on external lemmas that are not in this partition. The ones whose exact statements I would most want confirmed are `actual_A17_full_parent_energy`, `a18_top_contribution_le_nine512`, `a18_lower_absorption` and the definition of `a18BudgetScale`. Also external: `actualDerivativeCoordinate_support_drop`, `actual_derivative_rank_projection_energy_le`, `manuscript_A1_complex`, `typed_line/hyperplane_A1_operator_step`, `nestedCarrierEquiv`, `filteredCarrierFunction_rankProjection_zero_of_below_carrier`. The uses here are consistent and the numbers check out. |
| F2 | Integration | `a20_three_degree_global` | The cost hypothesis `_hcost` is unused, so `filteredCarrierFunction_energy_le_A16` must hold for every carrier with no cost condition. That is consistent with high-cost filters vanishing, but its statement should be confirmed in its own partition. |
| F3 | Integration / gap for A22 | Files 11–13 (Checks) | These are `#check` / `#print axioms` harnesses only. The statements and bodies of `manuscript_A22_actual`, `a22_positive_parent_from_lowerIH`, etc. are not in this partition, and the axiom outputs were not supplied. **The real-q A22 verdict (same selected consumer, no hHC premise) cannot be decided here.** |
| F4 | Integration | `manuscript_A21_actual` | Only dyadic p = 2^k with k ≥ 1 is covered. Real-q A22 needs an interpolation step for non-dyadic q. That step should be checked for exponent loss and any added premise. |
| F5 | Low | `manuscript_A6` docstring | The docstring says "orders above the degree contribute zero", but the statement keeps every term. The zero fact is the separate lemma `a6_mixed_zero_of_order_gt`, which is not used here. The guard `if 0 < a6Order t` is always true (`a6_order_pos`). This is a wording issue, not a soundness one. |
| F6 | Low | `manuscript_A20_raw_fourth_le` | Elaborated under `set_option backward.isDefEq.respectTransparency false`, and files 8 and 14 raise `maxHeartbeats`. Neither weakens kernel checking, but the GCP replay must keep these options to reproduce the build. |
| F7 | Info | SourceGlobal: `actual_fixed_functional_line_average_energy_le_two`, mixture/coset lemmas | These are conditional-sampling facts. Within this partition only `actual_source_parameter_nonneg` is visibly used downstream (via TransposeTransport). Whether the A17/A18 chain consumes the line-average bound is a cross-partition question. Do not read them as universal globalness claims. |
| F8 | Info | `transposeActualRestriction_order_le`, TransposeTransport header | The transposed order is only ≤ the original, which is the direction globalness needs. The file says explicitly that it does not identify the hyperplane draw with the line draw, which is the correct scope. |
| F9 | Info | `a6_one_pair_energy_le` | The codimension is written with the `V n` alias rather than `W n`. The two types are definitionally the same and `a6_codim_eq` reconciles them. Cosmetic. |
| F10 | Info | `quotientSectionCoordinates_of_kernel_line` | Stray leading space before `theorem`. Cosmetic. |

## Questions for integration

1. Exact statements of `a18BudgetScale`, `actual_A17_full_parent_energy`, `a18_top_contribution_le_nine512` and `a18_lower_absorption`. This partition assumes `a18BudgetScale = 2^(10Dr)·eps`.
2. The `manuscript_A22_actual` signature: real q, the same selected consumer, and no hHC premise. Also, where the dyadic A21 bound is interpolated to real q, and with what loss.
3. Statements of the A16 bound (cost-unconditional?), A19 (`2^(114D²)` form) and the DR6 bound (`/162`, `2^(6D²)`).
4. The `#print axioms` outputs for the three Checks harnesses.
5. Library trust in Init/Mathlib/Batteries rests on the pinned sources and was not re-reviewed. The Mathlib facts used here: `finrank_sup_span_singleton`, `exists_extend_of_notMem`, `card_linearIndependent`, `isIdempotentElemEquiv`.

None of the open gates you listed (Spectral47, source/star/robust8S/numericNO, reductions, runtime/learning, upstream bridges, manuscript/render/novelty) is affected or closed by this partition.
