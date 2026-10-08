# Full89 integration window 2/3 (analytic induction and incidence): non-claims review

## Verdict: GO-WITH-NOTES for this window only

- **Integration overall stays INCOMPLETE.** The HIGH contract and consumer questions from packet 7 (F1/F2) and the PseudorandomExact budget questions depend on files that are not in this window. I have kept them open below; this verdict does not close them.
- **Nothing was run.** I read the supplied text only and wrote nothing. Line numbers can't be checked without tools, so every citation is a declaration name.
- **Root's dispositions** were treated as hypotheses. Each one is either re-derived below or kept open.

## Bodies inspected: all 10 supplied, none skipped

| # | File (sha256 prefix) | Status |
|---|---|---|
| 1 | ActualBinaryMatrixHC46A11WeightedAggregate (B296A5A9) | inspected in full |
| 2 | ActualBinaryMatrixHC46DR6Convolution (CDDF6433) | inspected in full |
| 3 | ActualBinaryMatrixHC46DR6Incidence (31305E6B) | inspected in full |
| 4 | ActualBinaryMatrixHC46DR6Mobius (6E2CCA4E) | inspected in full |
| 5 | ActualBinaryMatrixHC46DR6Moment (500BF0B2) | inspected in full |
| 6 | ActualBinaryMatrixHC46DR6SignMoments (DAFA4306) | inspected in full |
| 7 | ActualBinaryMatrixHC46A18OriginalGlobalInduction (C4513E43) | inspected in full |
| 8 | ActualBinaryMatrixHC46A18InductionBounds (D583B3DA) | inspected in full |
| 9 | ActualBinaryMatrixHC46A20SquareGlobalness (435873CF) | inspected in full |
| 10 | ActualBinaryMatrixHC46A21DyadicMoment (2B3FE7D9) | inspected in full |

These are **not in this window**, so I could not inspect them: OriginalExactInhabitant, A22OriginalInduction, A22ParentFactorization, A22OperatorLq, RealQNorm, RealQTransport, SelectedComplementAnalyticMoment, SelectedComplementHC46OriginalApplication, BinaryMatrixFourier, ActualBinaryMatrixHC46, MatrixLift*, A7Transfer, A8Endpoint, A9Ambient*, A12, A16Final, A17Full.

## Per-finding dispositions

### W2-1: A11 discharges the strict-lower-degree hS for real (resolved for this window)

The chain inside A11, step by step:

- **The induction hypothesis is genuine.** `a11StrictLowerDegreeIH D` quantifies over every `e < D`, every `n d`, and every supported `g`.
- **The degree strictly drops.** `a11_actual_mixed_fourth_le_output_q` applies the hypothesis at degree `D - a6Order t`. Strict drop (`hlt`) follows from `hpos` and `horder`, and the support drop comes from `a7_output_binary_fourth`.
- **The A8 cost enters once per term.** `a8_output_q_le_actual_predecessor_sum` contributes `2^(6Dk)` with `k = rank(t1PullbackMap t)`. Its `_horder` premise is discharged by `horder`.
- **Orders above D are zeroed by proof.** `a7_derivative_fourth_zero_of_high` makes them exactly zero; they are not dropped by assumption.
- **The initial data are reindexed exactly.** `a11GlobalInitialEquiv` is a full bijection between outer `(A,B,t)` triples and actual `(C,H,X)` data. Both inverse laws are proved through `a7_carrier_parent_spec` and `a7_global_parent_unique`.
- **The A9 regrouping is exact.** `a11_weighted_actual_A9_partition` is an equality, through `a11GlobalA9SourceEquiv` and `a9AmbientA8PartitionEquiv`.
- **Overlap is actually paid for.** This answers the overlap Medium raised in packet 4 (proof F2 / complexity F1).
  - `a11_actual_fixed_final_saved_charge` charges every final fibre the coarse count `2^(3D(i+j+k))` from `a9Ambient_fixed_fiber_coarse_charge`.
  - Fibres outside the window have zero energy (`a11AmbientEnergy_zero_outside_window`).
  - Out-of-range `i` or `j` give empty fibres, proved by contradiction.
  - This also settles packet 5's question about the support-window case split.
- **The A10 saving checks out.** It needs `100(D−t)² + 27Dt + 6Dk ≤ 100D² − 63Dt − 4Dk`, which reduces to `100t² + 10Dk ≤ 110Dt` and holds because `k ≤ t ≤ D`.
- **The i/j tail and W6 finish close the bound.**
  - The `k=0` and `k≥1` tails are split correctly.
  - The rank weight satisfies `≤ 2^{-31D}/2^{6Dk}`.
  - The W6 step gives `≤ 2·Q`, so the total is `≤ 2^{100D²}·2^{1−31D}·Q`.
- **`manuscript_A7_actual`** builds the strict hypothesis by `Nat.strong_induction_on`, quantified over `n' d' g`, with base case `manuscript_A7_degree_zero`.

**Legacy helpers are not credited.** A11's source never names `a7_a9_preceding_output_sum_le`, `..._graph_charge`, `a7_a9_zero_parent_family_le`, `a9_initial_datum_card` or `a9_fiber_triple`. The A9 source uses the actual-fibre convention (`C ≤ A₀`, `B ≤ H` with codim `j`), not InitialGraph's inverted B₀. This absence is checked only in this one source and in the trace you supplied; I make no repository-wide claim.

**Caveats:**
- Root's line references (550/553, 713, 1207–1260) were confirmed at declaration level only.
- These correctness claims rely on the compiled types of `a7_positive_of_mixed_bound`, `a7_output_binary_fourth`, the A8 endpoint, the A9 coarse charge and `typedW6AllPairs_uniformT_le_two`. Their bodies were reviewed in packets 4 and 5, not here.

### W2-2: DR6 signed incidence and normalisation (resolved)

- **No double counting between F1 and F2.** `DR6Moment` splits each fibre into F2 and its complement, then injects the complement into F1 pairs (`dr6ComplementToF1Pair_injective`). This closes packet 5's F9 on the missing kernel-spanning condition.
- **The Möbius step is an exact identity.**
  - `dr6QBinomialAlternatingSum_eq_product` contains the factor `i=0`, so the product vanishes.
  - Grid factorisation reproduces `I + K − IK` exactly, with α₀ = 0 removing the (0,0) term.
  - The kernel side goes through the real dual-annihilator bijection (`dr6KernelSuperspacesEquiv`).
  - The complex selector equals `DR6OrdinarySelected` (`dr6_complexSelector_iff_actualOrdinary`).
- **Weights:**
  - α² ≤ 2^{Dk} only for 1 ≤ k ≤ D; grades above D are zero by support.
  - Carrier count ≤ 2^{2D(i+j)}, using rank X ≤ 2D; when rank X > 2D the coefficient is zero.
  - The rectangle factor is 31/225 for any cutoffs (r, s) once D ≥ 1.
- **Normalisation is consistent.** Both sides use complex Parseval against `uniformMean`. The right-hand side is the unrestricted sum over `(A,B) ≠ (⊥,⊤)` with weight `2^{7D(dim A + codim B)}`. A11 uses the same index type, `dr6ActualNonzeroABPairs`.
- **Proof-route difference (Low).** The F1 bound is proved through a Gram/Cauchy argument and gives factor 2 instead of the manuscript's Rademacher 81, so the /162 statement is weaker than what was proved. Statement fidelity against the manuscript is still unchecked.
- **Stale comments (Low).** Each of these says the work is incomplete when the code proves it:
  - the Moment header says the inequality is "uncompiled and uncertified";
  - the Convolution header says it "does not claim DR6";
  - the Incidence header says "remain open";
  - the Möbius header has a similar stale line.

  They carry no evidence weight in either direction.
- **Not a native root.** The DR6 theorem itself isn't among the 172 requested roots. Its axiom coverage holds only through transitive closure: the trace marks DR6Moment as consumed. Whether `manuscript_A6` consumes exactly this theorem is a cross-window check.

### W2-3: A18, A20 and A21 dependency direction and constants (resolved for this window)

- **A18.**
  - Confirmed: `a18BudgetScale D r eps = 2^{10Dr}·eps`. The inductions `ihD` (D' < D, any r) and `ihr` (r' < r) are non-circular. The D=0 and r=0 base cases are exact.
  - The scalar bounds hold: top contribution 1/512 + 8/512 = 9/512 ≤ 1/4, and lower absorption 1/2 + 2/961 ≤ 1.
  - `eps ≥ 0` is derived through `original_influence_parameter_nonneg`, not assumed.
- **A20.**
  - `filteredCarrierFunction_energy_le_A16` is called without any cost argument, so its compiled type is cost-unconditional. That closes packet 2's F2.
  - The budget is 2^{30D²}·2^{11D²} = 2^{41D²}, and 114 + 41 + 41 = 196.
- **A21.**
  - Recurrence: a(2q) − 4a(q) = 200q ≥ 196(q/2−1) + 114. The eps power is q − 1. Base cases: a(4) = 2800 ≥ 114.
  - The induction quantifies over all n, d, D and eps, so it can be applied to f² at degree 2D.
  - **The exponent p is a natural-number power of 2 only.** No real-p interpolation exists or is used.
- **Partial support for Root's "natural-dyadic p, real-conjugate q" correction.** The A18 output at r = D (2^{10D²}) and A21's form `2^{200D²p²}·E·eps^{p/2−1}` match the shapes packet 1 assumed. Whether the A22 body actually uses `pConjugate p` and these lemmas needs the A22 and RealQ bodies, so the correction is **kept open as a cross-window item**.
- **Fidelity question kept open (Low/Medium).** `OriginalActualInfluenceThrough` includes order 0 (the ambient energy is bounded by eps). In the final route this premise is always derived (from A16 in A20, and from the zero-cost energy in A22 per packet 1), so it doesn't affect the end-to-end theorems. Whether it matches the manuscript's definition is still open.

### W2-4: Native and trace evidence

- **Accepted as stated:** 172 standard profiles (two of them are subsets: `a21_exponent_le` = {propext}, `a21_density_recurrence` = {propext, Quot.sound}), all 7 exits zero, 319 source pins.
- **Warnings.** Zero OWNED warnings and zero inherited regressions is not the same as zero TOTAL warnings; the inherited debt remains open. The non-default option in A11 (`backward.isDefEq.respectTransparency false`) affects only the elaborator.
- **Comments carry no weight either way.** That covers the A11 "accepted at run 56" header, the stale "forthcoming A9" docstring, and the DR6 "uncompiled" text.

## HIGH and Medium questions this window cannot address (all kept open)

1. **HIGH (packet 7, F1).**
   - **Status: open.** Whether `original_HC46_exact` has type `HC46ExactContract` cannot be checked: its body is not in this window.
   - **The roots show one thing:** none of the 172 requested roots is a material-moment declaration.
   - **What that means:** if the type is confirmed, the universal theorem would be *logically available* to fill `hHC` in `selected_actual_material_moment_bound`. No dedicated hHC-free material export exists. `hSpectral` (Spectral47) remains a premise.
   - **Not established:** material-moment, reduction, runtime or learning acceptance.
2. **HIGH (packet 7, F2) and Medium (packet 8, F5).** Not in this window:
   - whether the contract is vacuous, and whether negative eta is excluded;
   - the zero-density branch;
   - nominal-budget padding and whole-fibre `exactWholeRestriction`;
   - `boolean_mean_le_of_exact`.

   Root's line-level claims about BinaryMatrixFourier and ActualBinaryMatrixHC46 are unverified here.
3. **Medium.** Also not in this window:
   - the guards on `exact_zoom_implies_nominal_pseudorandom` (`r < d`, strict full-row-rank, flag averaging, factor 2);
   - same predrawn T/f in `ActualLeafLabelRankImageAlignment`;
   - PseudorandomExact as a **one-sided** upper bound only, at exact budget r.
4. **A22 body.** Real conjugate q, `realQNorm_holder_nat_pow`, the A14 witness constants and the influence derivation are all outside this window.
5. **External statement shapes** relied on above: `a7_positive_of_mixed_bound` (the 162 terminal form), the A8 endpoint, the A9 coarse charge and partition, the W6 ≤ 2Q bound, `actual_A17_full_parent_energy`, A16, A19, `complexAmbientAffineRestrict_coordinate_global`, and A6 consuming DR6.
6. **Manuscript fidelity** (render and novelty gates). Open items:
   - the order-0 influence definition;
   - the constants 100, 24, 63, 31, 7D, 162, 41, 196 and 200;
   - the DR6 proof route.

   Also, A7's right-hand side `a7HybridQ` can be very large, so a useful bound depends on A12/A19, which are outside this window.
7. **Library trust.** The pinned Init, Mathlib and Batteries sources are trusted; I did not review their bodies.

## Safe claim boundary for this window

**What can be claimed.** This holds within the 10 inspected bodies, given the qualified native evidence, the compiled types of the listed external dependencies, and the pinned library trust:

- **A7.** `manuscript_A7_actual` holds for every finite binary-matrix space and every complex f supported through D. Its positive-degree hS is discharged by the genuine route: actual A8 endpoint, exact initial-data bijection, exact A9 partition, fibre charge, A10 saving, i/j tails, and W6. No legacy degenerate A7/A9 helper is referenced.
- **DR6.** `dr6_actual_complex_fourth_moment_over_162_le` holds with only the support premise. The signed Möbius identity is exact and the normalisation is consistent.
- **A18, A20, A21.** They hold with the constants shown above. A21 covers natural dyadic p ≥ 2 only.

**What cannot be claimed:**

- that HC46ExactContract is proved or non-vacuous;
- the real-q A22 statement;
- the hHC-free selected consumer, or any material-moment, Spectral47, numeric-NO, reduction, runtime or learning result;
- any upstream, fresh-checkout or final-provider gate;
- manuscript or render fidelity;
- zero total warnings;
- that legacy helpers are absent repository-wide;
- that Q is small or that the bound is numerically useful;
- any full-manuscript verdict.
