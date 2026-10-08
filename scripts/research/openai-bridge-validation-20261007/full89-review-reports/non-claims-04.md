# Non-claims review, partition 4/9: Full89 A22/HC46 selected consumer, file `ActualBinaryMatrixHC46A7Transfer.lean`

**Verdict: GO-WITH-NOTES, for this partition only.** This is not a verdict on Full89, HC46 or A22 as a whole.

The one supplied file was read in full, with no body skipped. I found nothing that blocks within this file's scope. There are 9 notes, none above Medium, and 7 open questions for integration.

**What I could and couldn't check.** I worked only from the pasted text, with no tools, so I didn't open the source index, the 172-theorem list or any imported module. That means I couldn't confirm which declarations here are on the 172 list. I also don't have exact line numbers, so references below use declaration names and where they sit in the file. I'm relying on your report of the GCP build (seven zero exits, no errors or warnings) for compilation; I didn't re-check whether any proof type-checks.

## File inventory

| File | SHA256 (as supplied) | Status |
|---|---|---|
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7Transfer.lean` | 32EB8395…B75FD | **Inspected**, every body read |

These imported modules weren't supplied in this partition, so I didn't review them; they belong to other partitions: A6Transfer, A9InitialGraph, A7HybridW6Transport, T2Transfer, A18OriginalGlobalInduction, FiniteDegreeFourier{Product,Reconstruction}, A1TypedFourier, A7EnergyConsumer, A7CarrierParseval, A12FourthMoment, A20SquareSupport, A1CharacterBridge, A1NestedCarrier.

## What the file establishes

**Proved with no extra hypotheses, for every finite `n, d`:**
- **`manuscript_A7_degree_zero`:** the fourth moment equals `2^(100·0·0) · a7HybridQ f`. The proof goes through `a7_constant_of_degree_zero`, `a7_filter_zero_of_positive_pair` and `a7_q_eq_zero_order`. The only assumption is Fourier support through 0.
- **`a7_degree_one_fourth_bound`:** the fourth moment is at most `2^100 · Q`.
  - `a7_mixed_sum_degree_one` discharges `hS` at D=1. Orders above 1 vanish (`a7_derivative_fourth_zero_of_high`), and order 1 is the saturated case (`a7_saturated_weighted_all_pairs_le`).
  - That in turn rests on the injection `a7_carrier_parent_unique` → `a7_global_parent_unique` → `a6_reconstruct_forward`, which is imported.
- **For every source `f`:**
  - `a7_q_ge_l2`: the squared L2 energy is at most Q.
  - `a7HybridQ_nonneg`.
  - `a7_hybridQ_smul`: Q scales by `|c|^4`.
  - `a7_saturated_all_pairs_fourth_sum_le`: the order-D mixed sum is at most `2^(6D²+1)·Q`.

**Conditional only.** The extra premise is part of the theorem statement, so none of these is a universal claim:
- **`a7_positive_of_mixed_bound`** assumes the mixed-sum bound `hS`. Its docstring says it is not manuscript A7.
- **`a7_positive_of_overlapping_shares` and `a7_mixed_sum_of_shares`** assume a share function `e` with a sum bound (`hshare`) and a per-triple bound (`hfourth`).
- **`a7_a9_preceding_output_sum_le` and `a7_a9_preceding_output_graph_charge`** assume a parent family with precedence (`hprec`) and selection (`hsel`).
- **`a7_one_hybrid_filter_sq_le_component`** assumes a real number `filterEnergy` with a bound `hle`.

**No hHC premise added:** no declaration takes an hHC-style hypothesis. The only analytic assumption throughout is `ComplexFourierSupportedThrough`, plus the explicit conditional premises listed above.

**Soundness markers:** no `sorry`, `axiom`, `native_decide` or `unsafe`. The large numeric facts use kernel `decide` on Nat values.

## Numeric exponent checks

I re-derived each of these by hand:

| Declaration | Inequality to show | Check | Result |
|---|---|---|---|
| `a7_terminal_factor` | 162·(2^-94D² + 2^(1-31D)) < 1 | At D=1 the value is about 162·9.3e-10 ≈ 1.5e-7; it decreases in D | ✔ |
| `a7_l2_slack` | 162 ≤ 2^8, and 8 + 6D² ≤ 100D² for D ≥ 1 | Direct | ✔ |
| `a7_triple_exponent_fits` | 100t² − 176Dt + 31D − 1 ≤ 0 on 1 ≤ t ≤ D | Convex in t, so the endpoints decide it: t=1 gives 99 − 145D, t=D gives −76D² + 31D − 1. Both are negative for D ≥ 1 | ✔ |
| `a7_triple_share_exponent_fits` | 100t² − 167Dt + 31D − 1 ≤ 0 | Endpoints give 99 − 136D and −67D² + 31D − 1, both negative | ✔ |
| `a7_saturated_pool_exponent_fits` | 30D² + 1 ≤ 100D² + 1 − 31D | Holds for D ≥ 1 | ✔ |
| `a7_middle_grassmannian_exceeds_share_slack` | 2^129 < [24 choose 12]₂ | [24 choose 12]₂ ≈ 3.46·2^144 | ✔ |
| `a7_gaussian_38_19_gt_order_one` | 2^360 < [38 choose 19]₂ | [38 choose 19]₂ ≈ 3.46·2^361 | ✔ |
| `a7_a9_multiplicity_le`, `a7_predecessor_fiber_le` | The case splits, including the factor 4 for proper subspaces | All cases close | ✔ |

**Proof direction:** every bound runs the stated way, an upper bound on the fourth moment or on mixed sums in terms of Q. The counterexample declarations (`a7OrderOne_output_q_exceeds_component`, `a7_rank38_character_q_exceeds_order_one`, `a7OrderOne_remaining_output_exceeds_leftover`) are strict lower bounds. They are stated and labelled as obstacles to a single-component charge, not as positive claims.

## Notes

1. **Medium (integration) — module header and docstring of `a7_degree_one_fourth_bound`.** Both say the A11 consumer in `ActualBinaryMatrixHC46A11WeightedAggregate` proves general A7, "accepted with notes at frozen run 56".
   - That claim can't be checked from this partition, and nothing in this file proves it.
   - It should not count as acceptance evidence.
   - General-D A7 is only conditional here, through `hS`.
2. **Medium (vacuity, already disclosed) — `a7_a9_preceding_output_sum_le` and `a7_a9_preceding_output_graph_charge`.**
   - The parent-family premises can be satisfied only degenerately: `a7_a9_zero_parent_family_le` sends every datum to the zero matrix, which ignores the graphs.
   - `a9FinalParent_not_both` / `a9ThetaParent_not_both` prove that the real rank-k datum parent can never meet both `hprec` and `hsel` against a rank-k final when k > 0.
   - So for the parent they are meant for, these theorems are empty. They must not be cited as an A9 charge. The docstrings already disclose this.
3. **Low — `a7_one_hybrid_filter_sq_le_component`.** The name suggests a statement about a hybrid filter, but `filterEnergy` is any nonnegative real at or below the full output energy. The content is plain monotonicity of squaring plus `a7_output_energy_sq_le_component`.
4. **Low (scope) — `manuscript_A7_degree_zero`.** The factor `2^(100·0·0)` is 1, so the result reduces to "fourth moment = L2² = Q". That is correct but trivial; it is the base case only.
5. **Low (definition fidelity, cross-partition) — `a7HybridQ`.** It is an unweighted sum over all pairs that includes `(⊥, ⊤)`. Whether this matches the manuscript's Q, and whether some other partition supplies a matching **upper** bound on Q (the header disclaims one), is outside this file.
   - That matters because Q can be very large: `a7_character_hybrid_q` counts selected pairs, for example at least [38 choose 19]₂ for rank 38.
   - So "fourth moment ≤ 2^(100D²)·Q" means little downstream without that upper bound.
6. **Low (instance hygiene) — local instances.** `attribute [local instance] Fintype.ofFinite` and `Classical.propDecidable` mean `a7HybridQ` and the cardinalities depend on how instances are chosen. Values are unaffected because `Fintype` is a subsingleton, but definitional equality with other modules' `Fintype` instances shouldn't be assumed at integration.
7. **Info — `set_option maxHeartbeats 1500000`.** This is a performance setting only, with no effect on soundness.
8. **Info — docstring placement.** The text "The zero-order pair is one nonnegative term… L2 energy is at most Q" sits on `a7_zero_order_uniform`, which is an equality. The `≤` statement is `a7_q_ge_l2`. Cosmetic only.
9. **Info — "the share hypothesis stays".** Many docstrings repeat this. It refers to `e` and `hshare` in `a7_positive_of_overlapping_shares`. `hS` in `a7_positive_of_mixed_bound` is a separate premise, and the header says A11 discharges it. These are two different premises and should not be merged at integration.

## Open questions for integration

1. Do `manuscript_A6` (fourth/162 ≤ 2^(6D²)·L2² + S), `a6_mixed_zero_of_order_gt`, `a6_reconstruct_forward`, `t1TripleToMap_injective`, `typedW6FilteredCarrierFunction_le_two` and the A7EnergyConsumer lemmas hold exactly as they are used here? They are defined in other partitions.
2. Does the A11 consumer really discharge `hS` with no added hHC premise, and do the unrestricted-eta HC46 and real-q A22 consumers call this file only through `a7_positive_of_mixed_bound` or the D ≤ 1 theorems?
3. Which declarations from this file are on the exact 172-theorem list? If any of the conditional or degenerate ones (Notes 2 and 3) are counted as standard-axiom roots, they should be labelled conditional.
4. Is the `a7HybridQ` definition faithful to the manuscript, and where is the matching Q upper bound proved?
5. The pinned kernel/library trust boundary (Init/Mathlib/Batteries). This file uses `decide` on Nat values around 2^360 and lemmas such as `Matrix.rank` and `Submodule.isComplEquivProj`. These are covered by the explicit library trust, not newly reviewed proof.
6. The provenance of the "frozen run 56" acceptance claim.
7. Everything listed as out of scope remains open: Spectral47, the source/star/robust8S/numericNO/encoded reduction/runtime/learning work, upstream bridges, and the manuscript, render and novelty gates.
