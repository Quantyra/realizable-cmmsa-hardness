# Non-claims review, Full89 partition 2/9

**Scope:** This review covers only the 18 complete files supplied in this partition. It does not judge the whole campaign, and it does not certify HC46, the A22 main theorem or the selected consumer as a whole; those parts are in other partitions. I used no tools and made no writes, so I did not open the source index. The verdict depends on the stated GCP results (seven zero exits, 172 standard axiom profiles, zero unresolved graph nodes). I could not count line numbers reliably without tools, so findings point to declaration names instead.

## Verdict: **GO-WITH-NOTES**

I read every supplied file in full and skipped none. I found no blocking defect, no vacuous premise, no hidden `hHC` premise and no reversed proof direction. Every numerical exponent I recomputed checks out. The notes below are fidelity and integration items, not proof errors.

## Inspection record

| # | File | Status |
|---|---|---|
| 1 | A18OriginalGlobalInduction | Inspected in full |
| 2 | A18QuotientSamplingLaw | Inspected in full |
| 3 | A18SourceConditioning | Inspected in full |
| 4 | A18SourceGlobal | Inspected in full |
| 5 | A18TransposeAverage | Inspected in full |
| 6 | A18TransposeTransport | Inspected in full |
| 7 | A20SquareGlobalness | Inspected in full |
| 8 | A20SquareSupport | Inspected in full |
| 9 | A21DyadicMoment | Inspected in full |
| 10 | A22OperatorLq | Inspected in full |
| 11 | A22OperatorLqChecks | Inspected in full (`#check`/`#print axioms` only) |
| 12 | A22OriginalInductionChecks | Inspected in full (checks only; its target module is not supplied) |
| 13 | A22ParentFactorizationChecks | Inspected in full (checks only; its target module is not supplied) |
| 14 | A6Transfer | Inspected in full |
| 15 | A7CarrierParseval | Inspected in full |
| 16 | A7EnergyConsumer | Inspected in full |
| 17 | A7HybridW6Transport | Inspected in full |
| 18 | A7PredecessorCount | Inspected in full |

## Main checks

**A18 (`actual_A18_original_global`)**
- **Hypotheses:** only `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eps f`. `eps` is unrestricted; `0 ≤ eps` is derived (`original_influence_parameter_nonneg`).
- **Quantifiers:** the outer induction on D generalises n, d, r, eps and f; the inner induction on r generalises n, d, eps and f. The calls to `ihD`/`ihr` on functions with different dimensions (the derivative coordinate, `fTop`, rank projections) are therefore valid.
- **Budget:** `a18BudgetScale D r eps = 2^(10Dr)·eps`, inferred from how `hpow`/`hmono` unfold it.
- **Top term:** 2·2^(10(D−1)(r−1)) + 4·2^(2D)·2^(10D(r−1)) ≤ (1/512 + 8/512)·2^(10Dr) when D, r ≥ 1. This matches `a18_top_contribution_le_nine512`.
- **Lower absorption:** 2·(Σ_{i<D} 2^(5ir))²·eps ≤ 2^(10Dr)/2 holds when r ≥ 1, because 4·(32/31)² ≤ 2^10. This is consistent with `a18_lower_absorption`.
- **Base cases:** D = 0 (f is constant) and r = 0 (the whole space) both give a budget of exactly eps.
- **Influence inheritance:** `original_influence_order_one_relative_reduction` has the right direction: outer cost = 1 plus inner cost ≤ D−1 gives a total ≤ D, using the exact additive cost in `relative_endpoint_cost_add`.

**A20**
- The cost condition is unused in `a20_three_degree_global` because the A16 bound covers every A, B, T. The resulting budget is 2^(30D²)·2^(11D²) = 2^(41D²) ✓.
- The raw fourth-moment budget is 2^(114+41+41)D² = 2^(196D²)·eps² ✓.
- The order bookkeeping (outer cost ≤ 2D plus inner cost ≤ D, total ≤ 3D) is exact.

**A21**
- The exponent recurrence needs 98q − 82 ≤ 200q, which holds.
- The eps powers combine correctly: eps · (eps²)^(q/2−1) = eps^((2q)/2−1).
- The induction statement quantifies over all n, d, D, eps and f. The base cases are p = 2 (trivial) and p = 4 (A19; 114 ≤ a21Exponent 4 = 2800).
- Only dyadic p ≥ 2 is claimed.

**A22OperatorLq**
- The coefficient bound is (1+2^j)(1+2^(j−1)) ≤ 2^(2j+1) ≤ 2^(3j) for j ≥ 1 ✓.
- Real q is kept throughout; only 1 ≤ q is required (Minkowski inequality and scalar multiplication).

**A6 / W6**
- The Hölder cost is (2^(ij))³ = 2^(3ij), and 7D(i+j) + 3ij ≤ 24Dt follows from i + j ≤ 2t ✓.
- The rank-k predecessor count is Gaussian(j, k)·2^(k(j−k)), with Gaussian ≤ 4·2^(k(j−k)).
- Each term with k ≥ 1 is at most 4/64^k, so the weighted sum is at most 1 + 4/63 = 67/63 ≤ 2 ✓.
- The degree-zero case is proved as an exact equality.

## Findings

1. **[Low, fidelity to integrate]** `OriginalActualInfluenceThrough` (A18OriginalGlobalInduction) includes the order-0 term: with A = ⊥, B = ⊤ it bounds the ambient energy E|f|² ≤ eps. The docstring of `original_influence_order_zero_seed` says this openly. Integration should confirm the manuscript's influence definition also includes order 0. On the A20 path it does no harm, since order-0 globalness already gives the same bound.

2. **[Low, statement scope]** The sum in `manuscript_A6` (A6Transfer) is not cut off at order ≤ D, even though its docstring says "orders above the degree contribute zero". That vanishing is a separate conditional lemma, `a6_mixed_zero_of_order_gt`. A consumer has to apply that lemma explicitly to truncate the sum.

3. **[Info, non-claim boundary]** The sampling results in A18SourceGlobal, QuotientSamplingLaw, SourceConditioning and TransposeAverage (`actual_fixed_functional_line_average_energy_le_two`, `actualA18TransposeAverage`, and others) are conditional infrastructure. `actual_A18_original_global` does not use them; it goes through A17 parent energy. The only things it pulls from these modules are the trivial lemmas `actual_fibre_base_mem` and `actual_source_parameter_nonneg`. They must not be cited as closing the source/star route, which is still open.

4. **[Info]** The A20SquareGlobalness header calls itself "a candidate for the coherent A20/A21 milestone, not certification". That self-description should be kept, not upgraded.

5. **[Info]** `set_option backward.isDefEq.respectTransparency false` appears on `manuscript_A20_raw_fourth_le`. It affects only the elaborator; the kernel still checks the proof.

6. **[Info, hygiene]** Leftover code:
   - the private `fibreEnergy_const_of_nonempty` is never used;
   - `hpartsEq` is never used in the two `actual_expanded_source_coordinates_coe*` lemmas;
   - an unused `let sCoord` sits in the statement of `actual_expanded_source_energy_le_two_common_coordinates`;
   - `hsmall` (≤ s−1) is stronger than needed.

## Questions left open for integration

- **External lemmas this partition relies on but does not contain:** `actual_A17_full_parent_energy`, `a18_top_contribution_le_nine512`, `a18_lower_absorption`, `a18BudgetScale`, `filteredCarrierFunction_energy_le_A16`, `manuscript_A19_actual`, `dr6_actual_complex_fourth_moment_over_162_le`, `t1Triple_card`, `manuscript_A1_complex`, `actualDerivativeCoordinate_support_drop`, `actual_derivative_rank_projection_energy_le`, the RealQ transport lemmas (`UpToActualLqGlobal_translate`, `_transpose`, `_rawLastColumn`/`_rawLastRow`), `actualGlobal_compose`, `raw_implies_actual`/`transpose_raw`, and the definitions of `UpToActualNormSqGlobal`, `fibreEnergy` and `lpMoment`.
- **A22 main theorem and HC46:** the checks files name `manuscript_A22_actual`, `a22_dual_energy_of_influences` and `a22_positive_parent_from_lowerIH`, but their bodies (A22OriginalInduction, A22ParentFactorization) are not in this partition. The real-q A22 statement, its use of the shared selected consumer, the unrestricted-eta HC46 statement and the absence of an `hHC` premise therefore cannot be confirmed here. The checks files' axiom output was not supplied either; I am relying on the 172-profile GCP claim.
- **External boundaries:** Init, Mathlib and Batteries are trusted at their pinned versions. They were not newly reviewed.
- **Still open:** Spectral47, source/star/robust8S/numericNO/encoded reduction/runtime/learning, upstream bridges, and the manuscript/render/novelty gates. This verdict does not affect any of them.
