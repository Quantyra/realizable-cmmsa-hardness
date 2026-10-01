```markdown
# Independent Final Review Report: Lean Conditional CMMSA Core
**Role:** Independent Reviewer
**Model Attestation:** Gemini 3.1 Pro (High)
**Context:** Actual independent final review of pinned Lean conditional core `ActualSelectedComplementAnalyticMargin.lean`. No commands or external tools were run; only read-only source review.

## Export Attestation
I explicitly attest that I have seen and reviewed the complete source for all three requested exports:
1. `original_score_and_failure_select_same_actual_moment_witness`
2. `original_score_and_failure_same_witness_contradiction`
3. `original_score_and_failure_yields_bad_zoom`

## Reviewed Files & Source-Line Findings

### `lean/PvNP/RealizableHardness/ActualSelectedComplementAnalyticMargin.lean`

*   **Lines 3024-3161 (`original_score_and_failure_select_same_actual_moment_witness`):**
    *   **Same A/f & Coordinate Mass Equality:** The witness extraction correctly extracts `fCoord` and defines `fSource = fCoord.comp ...`. The exact mass equality is strictly enforced without slack on lines 3120-3133 (`matchingStarMass ... fSource = matchingStarMass ... (coordinateFunctional ... fSource)`).
    *   **Dimension Saturated Subtraction:** Saturated subtraction `2 * h - c` is correctly guarded by `htle : c <= 2 * h` (line 3185), ensuring no underflow during the bounds translation. The dimension `c + m * s <= n` is explicitly carried forward.
*   **Lines 3356-3401 (`original_score_and_failure_same_witness_contradiction`):**
    *   **Contradiction Structure:** Correctly routes the exact strict inequality `2 * selected_actual_analytic_rhs < matchingStarMass` established in `selected_actual_fixed_functional_rhs_lt_matching_mass` against the upper bound proved in the moment caller. Real/Rat casts (`e : Rat` vs `(e : Real)`) are strictly controlled to prevent type-coercion vacuity.
*   **Lines 3586-3659 (`original_score_and_failure_yields_bad_zoom`):**
    *   **Quantifier Order:** The quantifier order correctly bounds the existential extraction. If the overall density score passes the threshold, it implies `∃ A, ∃ q, ∃ Q, ∃ P` such that the agreement exceeds the floor. The existential applies strictly to the side draws and complements.
    *   **Threshold Interpolation:** Correctly utilizes `exists_rat_btwn` to pick a precise rational `e` such that `floor < e < 2 * floor`, passing this strict constraint into the contradiction target.
*   **Lines 2681-2947 (`selected_actual_fixed_functional_rhs_lt_matching_mass`):**
    *   **Beta and Additive Signals:** The separation of the weighted `M/B` signal (`beta`) and additive `M/F` signal (`additiveRat`) is perfectly handled. `hhighActual` (line 2884) safely proves that both the `thresholdTerm` and the `highTerm` tails are fully absorbed by `additiveRat / 2`.

### `lean/PvNP/RealizableHardness/ActualOriginalFailureRowGenericFixedMomentCaller.lean`

*   **Lines 285-449 (`selected_actual_fixed_moment_bound_from_source_failure`):**
    *   **Exact Fixed Dyadic P:** Enforces $P = 2^{mK}$ where $K$ itself is a power of 2. This satisfies the strict `∃ q, p = 2^q` requirement of the `HC46ExactContract`.
    *   **Decay & Independent Rows:** Enforces $0 < \text{acceptedInverseDecayCoefficient } m P$ based purely on the dimensions, locking in the decay behavior for the exact moment parameter regardless of specific realization rows.

## Unsupplied Dependencies & Proof Limits
This review evaluates the conditional core structure and implications. The following dependencies are invoked but their internal proofs are not part of this snippet review, and must be trusted/reviewed separately:
*   **Analytic Numerics:** `ActualSelectedComplementAnalyticNumerics` definitions (decay coefficients, bounds, thresholds).
*   **Combinatorial Reductions:** `actual_side_score_selects_same_coordinate_functional` (pigeonhole), `source_failed_zoom_to_selected_coordinate`, and `actual_leaf_failed_zoom_gives_nominal_pseudorandom` (PR extraction from failed zoom).
*   **Unconditional Matrix Bounds:** `selected_actual_append_moment_row_generic`.
*   **Open Contracts:** The global implementations of `HC46ExactContract` and `Spectral47ExactContract` remain explicit obligations and are not proven here.

## Severity
**LOW:** No structural flaws, logical leaks, or vacuity issues were found in the conditional structure. The algebraic manipulation correctly honors the constraints.

## Verdicts

*   **Proof-Adversarial: GO**
    *   The structural translation from hypotheses to contradiction is tight. The math strictly guards against saturated subtraction underflows, prevents dimension mixing, and handles rational/real density casting safely. Quantifier order explicitly extracts the "bad zoom" witness against the universal hypothesis exactly as claimed.
*   **Complexity: GO**
    *   Scales are cleanly separated. The agreement floor correctly controls the low-degree HC norm scaling. $P$ is rigorously enforced as a dyadic integer, ensuring the invoked Fourier contracts are algebraically legal.
*   **Non-Claims: GO**
    *   The theorem statements are precisely scoped to the conditional core. They do not claim absolute resolution of the `HC46` or `Spectral47` contracts, nor do they claim unconditional hardness. They only claim the precise implication that a passing score forces a bad zoom.
```
