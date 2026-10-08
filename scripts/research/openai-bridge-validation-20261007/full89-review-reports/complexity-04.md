# Independent complexity review: Full89, partition 4/9

**File:** `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7Transfer.lean`
**SHA256:** `32EB8395…B75FD`, as supplied

**Partition verdict: GO-WITH-NOTES.** This covers only this file. It is not a verdict on the whole campaign or on HC46/A22.

**How I reviewed it:** I used no tools, wrote nothing and ran no subagents. I did not open the source index or any other file, so I relied only on the pasted text. The pasted text has no line numbers, so I cite declarations by name. Names are unique within the namespace. I checked statements, quantifiers, hypotheses, exponent arithmetic and proof direction by reading them. Whether the tactics actually succeed rests on the GCP evidence you supplied (zero exits, standard axioms); I re-ran nothing.

## Files

| File | Status |
|---|---|
| `ActualBinaryMatrixHC46A7Transfer.lean` | **Inspected**: every declaration and proof body read |

No supplied body was skipped.

## Scope

- **Unconditional results:**
  - `manuscript_A7_degree_zero`: the fourth moment equals `2^0·Q`.
  - `a7_q_ge_l2`: the squared L2 energy is at most `Q`, for every input.
  - `a7_degree_one_fourth_bound`: at degree 1, `fourth ≤ 2^100·Q`.
  - `a7_saturated_weighted_all_pairs_le`: the order-D part of the mixed sum is at most the allowance times `Q`.
  - The counting and energy injections, `a7_hybridQ_smul`, and the diagnostic examples.
- **Conditional results:** `a7_positive_of_mixed_bound` (premise `hS`), `a7_mixed_sum_of_shares` and `a7_positive_of_overlapping_shares` (premises `hshare`/`hfourth`). This file does **not** prove general positive-degree A7, and the docstrings say so.
- **Not in this file:** unrestricted-eta HC46, real-q A22, the selected consumer, and any `hHC` premise. Nothing here adds an hHC-style hypothesis.

## Checks

- **Hidden axioms:** none found. There is no `sorry`, `admit`, `native_decide`, `axiom` or `implemented_by`. `decide` appears only on closed Nat statements.
- **Quantifiers:** every theorem is universal over `n d : Nat`, including 0, with no hidden dimension lower bounds. `D > 0` is assumed only where it is needed (`a7_l2_slack`, `a7_terminal_factor`, `a7_positive_of_mixed_bound`, the saturated lemmas).
- **Exponent bounds:** I re-derived these by hand and they hold.
  - `a7_terminal_factor`: at D=1, `162·(2^-94 + 2^-30)` is about 1.5e-7, which is less than 1.
  - `a7_triple_exponent_fits` reduces to `100t² − 176Dt + 31D − 1 ≤ 0`. It is convex in t, and both endpoints (t=1 and t=D) are negative for D ≥ 1.
  - `a7_triple_share_exponent_fits` reduces to `100t² − 167Dt + 31D − 1 ≤ 0`, which holds the same way.
  - `a7_saturated_pool_exponent_fits`: `30D² + 1 ≤ 100D² + 1 − 31D`.
  - `a7_predecessor_fiber_le`: `2 + 2k(D−k) ≤ 3Dk` for k ≥ 1.
  - `a7_output_zero_share_le_original_component`: `4k(D−t) ≤ 9Dt`, using k ≤ t.
  - `a7_middle_grassmannian_exceeds_share_slack`: the Gaussian `[24,12]₂ ≥ 2^144 > 2^129`.
  - `a7_gaussian_38_19_gt_order_one`: `[38,19]₂ ≥ 2^361 > 2^360`. This is true but tight.
- **Proof direction:** consistent throughout. Upper-bound premises (`hS`, `hshare`) feed upper-bound conclusions, and `a7_q_ge_l2` is used as a lower bound on `Q`, scaled by a nonnegative factor.

## Findings

| # | Declaration(s) | Severity | Finding |
|---|---|---|---|
| F1 | `a7_positive_of_mixed_bound`, `a7_mixed_sum_of_shares`, `a7_positive_of_overlapping_shares` | Medium (integration) | General A7 for D ≥ 2 is only conditional here. The module docstring credits the discharge to the A11 file (`ActualBinaryMatrixHC46A11WeightedAggregate`), which is outside this partition. Integration must confirm that A11 discharges `hS` without new premises. |
| F2 | Module docstring; `a7_degree_one_fourth_bound` docstring | Low (documentation) | The comments say "accepted with notes at frozen run 56". That is an acceptance claim I cannot verify, and this review does not rely on it. |
| F3 | `a7_a9_preceding_output_sum_le`, `a7_a9_preceding_output_graph_charge` | Low–Medium (vacuity in intent) | The parent-family premises `hprec ∧ hsel` are only ever satisfied by the zero parent (`a7_a9_zero_parent_family_le`), which ignores the graphs. `a9FinalParent_not_both` proves the real datum parents fail these premises for k > 0 against a rank-k final. Integration must confirm no consumer uses these lemmas as a non-degenerate A9 charge. |
| F4 | `a7OrderOne_*`, `a7_rank38_character_q_exceeds_order_one`, `a7_selected_pairs_exceed_share_slack` | Info | These are deliberate counterexamples. They show that charging the whole output `Q` to one component fails, so they are not A7 claims. The nested-sum route (`a7OrderOne_output_q_le_original_q`, `a7_preceding_character_q_le_original`) is the valid one, and it is proved only for characters. |
| F5 | `a7_rank_zero_output_q_eq_nested`, `a7_preceding_*`, `a7_zero_pullback_output_zero_share_avg` | Info | These hold only for character inputs, zero pullbacks, or the zero-order output share. The docstrings say a general complex input is open. |
| F6 | The two `decide` theorems, under `attribute [local instance] Classical.propDecidable` | Info | `decide` only succeeds if the computable Nat instance is the one chosen, so the kernel checked these proofs. This is a fragility concern, not a soundness one. |
| F7 | `set_option maxHeartbeats 1500000` | Info | Build hygiene only. |

## Open questions for integration

1. **External definitions.** I inferred these from how this file uses them and did not check them:
   - `Selected` (I read it as `A ≤ range Y ∧ Y⁻¹A ≤ B`)
   - `ComplexFourierSupportedThrough` (coefficients vanish when rank > D)
   - `typedW6QComponent` (carrier energy, squared)
   - `a6Order`, `dr6ActualNonzeroABPairs`, `T1IndexTriple`
2. **Imported lemmas this file relies on:**
   - The exact statement of `manuscript_A6`.
   - `a6_mixed_zero_of_order_gt` and `a6_reconstruct_forward`.
   - `typedW6FilteredCarrierFunction_le_two`.
   - The `A7EnergyConsumer` lemmas.
   - `manuscript_A1_complex`.
   - The `w6_card_*`, `a9_inducing_card`, `a9_initial_datum_card` and `t2_*` lemmas.
   - Carrier Parseval.
3. **A11's use of this file:** whether A11 discharges `hS` without the F3 lemmas and without an hHC premise.
4. **Out of scope here:** unrestricted-eta HC46, real-q A22, and the shared selected consumer all need auditing in their own partitions.
5. **Library trust:** Init, Mathlib and Batteries are trusted at their pinned versions, not reviewed here.

All the gates you listed as open beyond this partition remain open.
