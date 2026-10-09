# Independent non-claims review: spectral manuscript, primary-source and actual-caller crosswalk

**This review is not final acceptance.** I used no tools, wrote nothing, ran no Lean or Lake and launched no subagents, and I did not recompute any SHA-256. Every hash and status below is copied from the packet. Everything here comes from reading the supplied text, which counts as informal reading evidence, not native or kernel evidence.

## 0. Verdicts

| Question | Verdict |
|---|---|
| **M1 source-shape alignment** | **Aligned at the reading tier.** The manuscript's T, 𝒢, Φ, invariance hypothesis, restricted adjoint and squared normalization match MZ v1 §4.2 (the `lm: not increase norm` lemma) and MZ24 Appendix A.10–A.13, after the notation differences listed in §3 are resolved explicitly. Remaining M1 debt is citation custody: archive identities, lemma numbering and the custody document were not supplied. |
| **Is the full exact argument sufficient?** | **Yes, as prose.** I checked the manuscript lemma and its proof, and the current argument, step by step. I found no mathematical error. The exact eigenvalue and the exact energy formula are our own reconstruction. MZ states only the weaker bound. |
| **Actual consuming application** | **Not complete (HIGH).** The frozen candidate removes the Spectral47 premise from exactly one legacy-namespace, selected-leaf, high-energy lemma. Every supplied material/SourceSize/dyadic caller still takes `hSpectral`. No supplied body discharges HC46 and Spectral47 together. |
| **Native / manuscript final readiness** | **Not ready.** Full101, the selected-leaf application and the exact-energy candidate are all uncompiled. GCP authentication is still pending. Numeric NO, source/runtime/upstream debt and R14 HIGH remain open, and novelty/citations/PDF/provider/publication are open. **There is no overall GO.** |

## 1. Coverage

**Fresh complete reads (8 new file bodies):**
1. `paper/submission-manuscript.md` (6F8D…). I read it in full. Acceptance scope is only the finite-spectral lemma, the matrix-lift/inverse-agreement caller, and the appendix interface used by that caller.
2. `primary/mz-v1-source.tar/k_query_grassmann.tex` (1950…).
3. `primary/mz24-arxiv-v4-source.tar/appendix_sections/Fourier_appendix.tex` (A80A…).
4. `ActualFixedFunctionalBinaryMatrixMoment.lean` (87CC…). This is the module that defines the coordinate equivalence.
5. `ActualSelectedComplementSourceSizeOriginalApplication.lean` (22DE…).
6. `ActualSelectedComplementManuscriptDyadicMoment.lean` (AF3E…).
7. `ActualSelectedComplementSpectral47OriginalApplication.lean` (9261…).
8. `…Spectral47OriginalApplicationChecks.lean` (AA4F…).

**Additional sections read in full (these are not files):**
- The current argument (76DF…).
- The source-alignment audit JSON (5229…).
- The prior root reconciliation (BB18…) and all three prior reports (126C…, 1AE7…, 50EB…). Their SHA labels agree with the reconciliation's records.

**The 33 prior bodies were reused by identity.** I do **not** claim a fresh full review of all of them. I re-consulted these only for cross-reference:
- the legacy and SourceSize `…AnalyticMoment` modules;
- `…Spectral47ExactInhabitant`, `…ExactImageEnergy` and `…FrameProductRatio`;
- `…AppendSpectral47`, `…CrossLevelOrthogonality`, `…RightFourierCovariance` and `BinaryMatrixFourier`.

**Scope limits:** Full101 captures 340 sources in total, and I make no claim about all of them. Full100 native GREEN covers only its 327 sources.

**Status labels on the new bodies:**
- The new sections carry **no NATIVE_STATUS tag**.
- Two bodies match Full100 native identities by source SHA (22DE… and AF3E…). Their in-file banners ("not been compiled", "Uncompiled candidate") are therefore stale historical bytes.
- `ActualFixedFunctionalBinaryMatrixMoment` (87CC…) does **not** appear among the report's eight added identities, so this packet does not pin its native status.
- The Spectral47OriginalApplication and Checks files are frozen and unlaunched.

## 2. Findings

| # | Finding | Severity | Evidence | Disposition / action |
|---|---|---|---|---|
| **F1** | **M1 operator shape now aligned.** MZ v1 defines `T F(M)=E_{v}[F([M,v_1..v_{2δℓ}])]`, with unconditional uniform appended columns. The manuscript has `(𝒯F)(X)=E_B F([X,B])` with B unrestricted. Lean `appendAverage` is a uniformMean over every `BinaryMatrix n s`. MZ24 defines 𝒢 by full-column-rank A (2ℓ×2(1−δ)ℓ), and Φ with unrestricted `B∈F^{n×2δℓ}` and full-row-rank `C∈F^{2δℓ×2ℓ}`, sampled independently. The manuscript's 𝒢 and Φ are identical. Basis invariance (`F(MA)=F(M)` for full-rank A, every M) equals Lean's paired-inverse `basisInv`. | was HIGH, now **closed (shape)** | MZ v1 operator definition; MZ24 A.11 and A.12 statements and proofs; manuscript `lem:finite-spectral` | Closed at the informal tier. Custody items are in F12. |
| **F2** | **Restricted adjoint.** MZ24 A.11 needs invariance only of F (the first argument). The manuscript says explicitly: "No invariance of H is required; the identity is not asserted for arbitrary first arguments." I checked the substitution N=MA, which turns `H(MJ_0)` into `H(NA^{-1}J_0)`. Here `A^{-1}J_0` is the first c columns of A⁻¹, which is uniform full-column-rank by constant completion fibres. Orthogonality and the norm identity use the adjoint only with first argument `F_i`, which is invariant because rank-preserving χ indices are permuted. | Info | Manuscript adjoint display; MZ24 A.10/A.11 | Correct. No unrestricted adjoint is claimed. |
| **F3** | **The exact eigenvalue and exact energy are our reconstruction, not quotations.** MZ24 A.13 gives only `|λ| ≤ 3q^{t−n}+q^{−t(2δℓ−1)}`. MZ v1 Lemma 4.7 gives only the squared weaker bound. The manuscript's `λ_S=Pr_C[SC^T=0]`, `λ_i=∏_{j<s}(2^{d−i}−2^j)/(2^d−2^j)` (0 when s>d−i), and `‖𝒯F_i‖²=λ_i‖F_i‖²` are stated as "We reconstruct…". | Low (wording is adequate) | Manuscript proof opening; MZ24 A.13 statement | Keep the "reconstruct" attribution. Do not cite A.13 as the source of the equality. |
| **F4** | **Source notation inconsistencies, preserved and not normalized.** Items (a)–(l) in §3. None is load-bearing, because the manuscript proof is self-contained and typed. | Medium (citation hygiene) | §3 | Record them in the crosswalk. Resolution status is per item in §3. |
| **F5** | **Is the full exact argument sufficient?** Re-derivation in §4 found no error. This includes the c/s/i/n zero branches and agreement of the two independent routes. | Info | §4 | Sufficient as prose. Native translation is still owed (N1). |
| **F6** | **Actual consuming application gap.** `ActualSelectedComplementSpectral47OriginalApplication` imports and opens the **legacy** `ActualSelectedComplementAnalyticMoment` and proves `selected_leaf_high_energy_le_spectral_original_application`. That lemma only instantiates legacy `selected_leaf_high_energy_le_spectral` with `spectral47_exact_contract_inhabitant`, for an arbitrary coordinate leaf table T and functional f. It has no I/copies/U/A/C, no center, no m-moment, no failed-zoom/PR, no HC46 and no mass bound. **`hSpectral` is still a premise in** SourceSize `selected_actual_material_moment_bound`, SourceSizeOriginalApplication `…_original`, ManuscriptDyadic `…_at_dyadic_exponent` and `…_original_at_dyadic_exponent`, and legacy `selected_actual_HC_spectral_moment_bound` / `selected_actual_material_moment_bound`. | **HIGH** (claims hygiene and application; mathematical risk is low) | New file body; caller signatures | Do not call this a source, table or runtime completion. Write a SourceSize-namespace original application that passes `(spectral47_contract_iff c).mp (spectral47_exact_contract_inhabitant c)` together with `original_HC46_exact` into the material and dyadic consumers. Then compile it and trace it. |
| **F7** | **Legacy namespace conflates source rows with m.** Legacy `selected_actual_material_moment_bound` and `selected_actual_source_dimension_bound` take `I : Instance N m`. SourceSize separates `rows` (report: `source_row_independence_native_verified: true`). The whole Full101 chain imports the legacy module. The wrapper itself never touches `I`, so nothing is wrong yet. A legacy material route would inherit the conflation. | Medium | Legacy vs SourceSize signatures | Consume only through SourceSize. Keep rows independent of the fixed m. |
| **F8** | **The contract targets only the weaker inequality.** `Spectral47ExactContract` encodes `≤ (2^{−i(s−1)}+3·2^{i−n})·energy`. Its RHS matches MZ v1 Lemma 4.7 verbatim with q=2, s=2δℓ, δ↔ρ, ℓ↔h, and its squared normalization matches too. The manuscript lemma additionally states exact equality, λ_i, 0≤λ_i≤2^{−is}, 𝒢𝒯=Φ and the restricted adjoint. None of these has a Lean target type. The uncompiled exact-energy candidate gives only the frame-ratio form. The manuscript's caller (`lem:inverse-explicit`) consumes only orthogonality (native, Full100) and the weaker bound. | Medium | Contract text; manuscript inverse-lemma "supplies cross-level orthogonality and the unchanged spectral bound" | The exact clauses are not on the caller's critical path. They **are** needed before anyone says "manuscript lemma as stated is natively verified". |
| **F9** | **Parameter mapping.** δ↔ρ; ℓ↔h; d=2ℓ↔c+s=2h; s=2δℓ↔`leafK`=2ρh; MZ `k`↔Lean/manuscript `m` (leaf arity); MZ `t`↔manuscript T and P↔Lean dyadic `k`; r=10m/ρ; n↔2J; q=2. **(a)** The fixed-window SourceSize consumer forces 4m≤k<8m. The manuscript needs P ≥ mT with T ≥ 4(m+3)/(mρ) and ρ ≤ 1/4000, which generally exceeds 8m. Only the ManuscriptDyadic caller (any dyadic k≥4m) is compatible. **(b)** Lean's Hölder uses exponent k/m, giving β^{1−m/k} ≤ β^{1−1/T} when k ≥ mT and β ≤ 1, and `(2e)^{m−2m/k}` matches the manuscript's `(2e)^{m−2m/P}`. **(c)** Lean J = `SamplerParameters.blocks samplerA h`. That body is unsupplied, so identifying it with the manuscript's J=2^{2^{Ah²}} is unverified. | Medium | Dyadic module; manuscript inverse lemma | Bind manuscript P to the dyadic k and check the J definition. The fixed-window theorem is not the manuscript route. |
| **F10** | **Caller reductions are not formalized.** Lean's RHS keeps `Σ_{i>r}(2^{−i(s−1)}+3·2^{i−n})E[F_i²]`. These manuscript steps have no supplied Lean counterpart: the reduction to `2^{−(r+1)b}+3·2^{2h−n} ≤ 2^{−rb}` (I checked it needs exactly n ≥ 2h+rb+log₂6), the choice a=η, the averaging over f, the ambient lower bounds, and the λ>0 contradiction. The factor-2 matrix bound's `hsmall` is discharged inside the unsupplied `selected_actual_append_moment`. Lean's condition `(c+ms)2^{2h−1−n} ≤ 1/2` is weaker than, and implied by, the manuscript's `(2h+2ρmh)2^{2h−n} ≤ 1/2`. | Medium | Analytic caller; manuscript inverse lemma | Translate or review the remaining caller steps. Review `…SourceSizeAppendMoment`. |
| **F11** | **Squared vs ordinary contraction is consistent.** The spectral contract and MZ Lemma 4.7 are squared L² (ratio = λ_i). Low levels use ordinary Jensen L^p contraction (`appendAverage_lpNorm_le`; MZ `‖TF^{=i}‖_{kt} ≤ ‖F^{=i}‖_{kt}`). The manuscript notes that the unsquared L² factor is √λ_i. No mismatch found. | Info | Contract; manuscript; MZ v1 | None. |
| **F12** | **Citation and version custody.** The packet supplies member files only. It does not supply archive hashes, arXiv version identifiers, preambles or main .tex, PDFs, or the cited custody file. Numbering inferred from counter order: MZ v1 Lemma 4.7 = `lm: not increase norm` and Theorem 4.6 = th:EKL, both consistent with the manuscript's citations; MZ24 A.10–A.13 = level-d invariance, adjoint, Φ, eigenvalue, consistent with MZ v1's in-text citations. MZ v1 cites "A.18" for preserve-pseudorandom. That resolves to A.17 or A.18 depending on whether the claim environment shares the theorem counter, which can't be settled without the preamble. | Medium | Primary members | Supply archive and PDF identities and the custody doc. Confirm numbering from compiled PDFs. |
| **F13** | **Evidence-tier labelling.** There are stale banners in two Full100-matching bodies. The status of 87CC… is not pinned here. The Checks file only does `#check` and `#print axioms` on the one wrapper. It has no SourceSize-shaped `example : …Spectral47ExactContract c := …` check and has never run. | Low | Banners; native report | Keep banners as historical bytes, and get status from the report. Add SourceSize-shaped checks in a new, separately reviewed candidate. Don't edit frozen Full101. |
| **F14** | **Real vs complex scope.** The manuscript and MZ24 use complex L² with ⟨F,H⟩=E[F H̄]. The Lean contract quantifies real F only. Every consumed F is a real Boolean lift, so this is sufficient for the callers. | Low | Contract vs manuscript | State "real-valued F" in the crosswalk. |
| **F15** | **Notation overloading in our own argument.** It uses `G(k,i)` (frame count), `G H(M)` (the operator 𝒢), `H(t)` (Gaussian product) and generic `H` in ⟨TK,H⟩. Lean `selectedG` is the center indicator, not 𝒢, and no Lean operator 𝒢 exists. The argument's fixed-image section still describes a dualMap route, while the Lean uses independent rows. | Low | Current argument | Rename to e.g. 𝒢, Fr(k,i), H₂(t), and update the duality prose. |

## 3. Primary-source notation issues (F4), with how each is resolved

| | Source location | Inconsistency | Resolution |
|---|---|---|---|
| a | MZ24 A.11 statement | "G ∈ L₂(…)", but the conclusion says ⟨F, 𝒢H⟩ | The manuscript uses 𝒢 for the operator and H for the function. Resolved in prose. |
| b | MZ24 A.11 proof | "A⁻¹J uniformly random in F_q^{n×2(1−δ)ℓ}" should be 2ℓ×2(1−δ)ℓ | The manuscript's `A^{-1}J_0` is typed d×c. Resolved in prose. |
| c | MZ24 A.13 proof | Normalizes `SA^T`, then rewrites `χ_S(BCA^T)=χ_{SA}(BC)` with the transpose swapped | Typed form `χ_S(BC)=χ_{SC^T}(B)`, consistent with A.8. Lean `pairing_mul_right_transpose` (Full101, uncompiled) and `character_mul_right` (Full100 native) fix the orientation. **Φ-eigen orientation has no Lean declaration; still open.** |
| d | MZ24 A.15 proof vs A.13 statement | Uses `q^{−2dδℓ}+3q^{d−n}`, which is stronger than A.13's printed `q^{−d(2δℓ−1)}` | Justified for q=2 only by our exact λ_i ≤ 2^{−is}. Not supported by A.13 as printed. Record this; the manuscript and Lean use the weaker printed exponent. |
| e | MZ24 A.14 proof | The 𝒯F^{=d} expansion via "M′, S′ removing columns" is garbled | Replaced by native `appendAverage_character` (tail-zero kill). Resolved. |
| f | MZ24 bilinear intro | (n−2ℓ)×2ℓ carrier dimensions are never used | Not used anywhere. |
| g | MZ v1 Lemma 4.8 proof | Index typo `F^{=d}`; also bounds `3·2^{i−n}` for i>r by `3·2^{r−n}`, which is the wrong direction | The manuscript uses `3·2^{2h−n}` and n ≥ 2h+rb+log₂6. Resolved in the manuscript; not formalized (F10). |
| h | MZ v1 Lemma 4.4 | Event 𝖠 / complement direction garbled | The manuscript's matrix-sampler factor 2 replaces it. Lean `matchingStarMass_cast_le_twice_actualBinaryMatrixMoment` exists (dependency bodies unsupplied). |
| i | MZ24 A.12 proof | The translation W ↦ W + MA₂ is implicit | Stated explicitly in the manuscript and in our argument (B ↦ B − MS). Resolved in prose. |
| j | MZ v1 Lemma 4.7 | Prose says "close to 2^{−2dδℓ}"; the statement says 2^{−d(2δℓ−1)} | The contract uses the statement form. |
| k | MZ v1 | `G` is the center indicator, `\mc{G}` is the operator | Distinct macros. The manuscript keeps the distinction. |
| l | MZ24 `eq: define F from L` | Text says "H", the display defines G | Not load-bearing. |

## 4. Mathematical check of the manuscript lemma and the current argument

I checked each of the following.

- **Adjoint.** See F2.
- **𝒢𝒯F = ΦF.** Steps:
  - A=[R,A₂] is uniform in GL(d) because every R has the same positive number of completions, ∏_{j=c}^{d−1}(2^d−2^j).
  - Translate W ↦ W + MA₂.
  - Then F(MA+[0,W]) = F(M+[0,W]A⁻¹) = F(M+WC), where C is the last s rows of A⁻¹. C is uniform full-row-rank by constant row-completion fibres ∏_{j=s}^{d−1}(2^d−2^j). W is independent of A, hence of C, and is never rank-conditioned.
- **Eigenvalue.**
  - `χ_S(BC) = χ_{SC^T}(B)`. Averaging over unrestricted B gives [SC^T = 0], which says every row of C lies in the (d−i)-dimensional right kernel of S. So λ_i = G(d−i,s)/G(d,s).
  - Each factor satisfies `(2^{d−i}−2^j)/(2^d−2^j) ≤ 2^{−i}`, since `2^{−i}(2^d−2^j) = 2^{d−i}−2^{j−i} ≥ 2^{d−i}−2^j`. Hence 0 ≤ λ_i ≤ 2^{−is}.
- **Norm and orthogonality.** ⟨𝒯F_i, 𝒯F_j⟩ = ⟨F_i, ΦF_j⟩ = λ_j⟨F_i, F_j⟩.
- **The two routes agree.** Factoring 2^j out of each factor shows the frame ratio G(c,i)/G(d,i) equals λ_i. Spot checks: (c,s,i) = (1,1,1) gives 1/3; (2,1,1) gives 3/7; (1,2,1) gives 1/7 by both routes, since G(2,2)/G(3,2) = 6/42. (1,1,2) gives 0.
- **Natural/real zero cases.**
  - The manuscript's explicit branch "λ_i = 0 if s > d−i" avoids negative real factors.
  - Lean `frameProduct` uses truncated ℕ subtraction. It is exact because the j=k factor is already 0 whenever some j > k appears.
  - Hazard for a future formal λ: i > d with s = 0. Truncated d−i = 0 gives an empty product = 1, while integer d−i < 0 gives 0. It is harmless because F_i = 0 there, but a formal λ definition must guard i ≤ d or use integer subtraction.
  - Other boundaries: n=0, c=0, s=0, i=0, i>c, i>n and d=0 all hold.
- **Weaker estimate.** 2^{−is} ≤ 2^{−i(s−1)} + 3·2^{i−n}. The +3 term is pure slack. That explains the unused additive term and the unused ρ/height/parity guards that the prior reviewers flagged.

## 5. Which spectral premises the frozen candidate actually removes

- **Removed:** the `hSpectral` argument of legacy `selected_leaf_high_energy_le_spectral` only. This holds once compiled; it is not compiled yet. All guards are retained and passed through: hEven, hRho, hc, hs and `hHeight : sourceHeightCutoff ρ ≤ h`.
- **Remaining downstream premises:**
  - `hSpectral` in every material and dyadic consumer (F6).
  - `hsel`, `hA`, `hrd`, `e ≥ 0`, `hfail` (failed-zoom on the same `selectedCoordinateLeafTable I copies U A T`), `a > 0`, and the dyadic k with 4m ≤ k.
  - In the non-`_original` variants, `hHC`.
- **Preserved in the SourceSize chain (as read, not re-proved):**
  - One common I/copies/U/A gives Cc, Tc and fc.
  - The PR premise and the mass bound use that same Tc and fc.
  - m is fixed by `hsel` and is the matchingStarMass arity.
  - The source-height, parity, ρ and split guards come from the unsupplied `selected_spectral_parameters`.
  - `c+s ≤ n` comes from h² < J.
  - HC46 is consumed per level i ≤ r with η = 2e, matching the manuscript's δ = 2e.
- **Discharged elsewhere:** `original_HC46_exact` discharges HC46 in SourceSizeOriginalApplication and in the dyadic `_original` variant. Those bodies match Full100 native SHAs, but the inhabitant's own body was not supplied. **No supplied body discharges HC46 and Spectral47 together.**

## 6. Unsupplied prerequisites that affect this scope

- **Project modules:**
  - `ActualSelectedComplementSourceSizeAppendMoment`: mass bound, center identity, `hsmall` discharge.
  - `ActualSelectedSpectralParameters`: ρ value, the hc/hs/hcut facts, `leaf_split_total`, `analyticSourceHeightFloor`.
  - `ActualBinaryMatrixHC46OriginalExactInhabitant`.
  - `ActualLeafLabelRankImageAlignment`.
  - `ActualRankImageRightBasisInvariance`.
  - `ActualFiniteMomentLpBounds`.
  - `MatrixGrassmannIdentity`: rawF/rawG/rawTF/matrixMoment, `grassmann_le_twice_moment`, `matrix_grassmann_identity`.
  - `ActualFixedFunctionalStarMoment`, `ActualOrdinaryStarWeightedSelection`, `ActualSourceStarLaw`.
  - `ActualComplementCoordinateMassBridge` (the selectedCoordinate tables).
  - `ActualTagged*`, `ActualCmmsaAdmissibilitySelector`, `ActualCmmsaParameterReconciliation`, `ActualStarFixedRhoDimensionGuard` (leafT/leafK), `SamplerParameters.blocks`, `MatrixLiftNominalDirectComparison`, `ActualMaximalPairLadder`, `ActualOccurrenceAllocation`.
- **Mathlib:** Matrix/Basis, Dual/Basis, Projection, RankNullity, GL Defs, `equiv_linearIndependent`, `card_compl_set`, `MeanInequalities` (`compact_inner_le_weight_mul_Lp_of_nonneg`), `Finset.expect`.
- **Primary sources:**
  - MZ v1 and MZ24 v4 archive identities, preambles and main tex, and compiled PDFs (for numbering).
  - MZ24 body statements cited by MZ v1, e.g. Theorems 5.1–5.3.
  - EKL Theorem 5.5, Proposition 3.6 and Theorem 1.13. These are cited, but the manuscript appendix reconstructs them.
  - The custody file `openai-math-novelty-citation-reconciliation-2026-10-07.md`, `SOURCES.md` and `REVIEW.md`.
- **Audit inputs:** the audit's input archive (2B03…) and manifest (8E71…). The audit's six source SHAs and fourteen declaration statements agree with the supplied bodies by label. The audit pins the **SourceSize** contract while Full101 inhabits the **legacy** one; the native `spectral47_contract_iff` (Iff.rfl) bridges them. The audit itself records `mathematical_implication_reviewed: false` and `compiler_invoked: false`.

## 7. Non-claims and evidence tiers

- **Native:** Full100 GREEN only, for its 327 sources: cross-level orthogonality, covariance/orbit, the contract bridges, the SourceSize original and dyadic callers. The report has `accepted: false` and `consumption_trace_complete: false`.
- **Uncompiled:** all eleven Full101 recovered sources, the Spectral47OriginalApplication and its Checks, and the exact-energy candidate with its checks.
- **Prose only:** the exact λ formula, 𝒢𝒯 = Φ, the completion marginals, the restricted adjoint and the H-factorization.
- **Attribution:** the spectral method is MZ Lemma 4.7 / MZ24 Appendix A.10–A.13. The counting results are existing Mathlib. Our exact equality is a reconstruction.
- **Not claimed:** novelty, priority, source or runtime results, fresh-checkout replay, full-340 or full-327 body review, manuscript acceptance, validity of the whole manuscript, or publication GO.
- **Not touched by this crosswalk:** numeric NO, source/star/robust8S/pre-draw/sampler/encoded-reduction/runtime/learning/upstream debt, and R14 HIGH.

## Remaining to-do list

1. Renew GCP authentication. Natively certify frozen Full101 and its selected-leaf application/Checks **unchanged**, with source, dependency and axiom identities and real warning diagnostics. Separately certify the exact-energy candidate.
2. As a new, separately reviewed candidate, write and compile a **SourceSize-namespace** original application: pass the inhabitant through `spectral47_contract_iff` into the material and **dyadic** consumers, together with `original_HC46_exact`. Keep rows independent of m, and keep the common I/copies/U/A/C/T/f and every guard. Add SourceSize-shaped `example` checks. Trace actual consumption.
3. Define Lean target types for the manuscript lemma's exact clauses (λ_i, exact energy, 𝒢, Φ, restricted adjoint, 𝒢𝒯 = Φ), and translate them natively. Prove natively that the frame ratio equals λ_i, with explicit zero branches and an i ≤ d guard.
4. Bind manuscript P/T to the dyadic k. Verify `SamplerParameters.blocks` against the manuscript's J. Formalize or review the caller reductions: the high-level sum to 2^{−rb} with n ≥ 2h+rb+log₂6, the threshold a=η, the f-selection averaging, the ambient bounds and the λ>0 contradiction.
5. Supply and review the unsupplied project and Mathlib bodies listed in §6. These include the append-moment `hsmall` discharge, the spectral parameters and the HC46 inhabitant.
6. Citation custody: archive hashes, arXiv versions, PDFs, numbering confirmation (including MZ24 A.17/A.18), the custody document, and a crosswalk entry recording items (a)–(l).
7. Clean up our own notation (𝒢 vs the frame count vs Gaussian H) and the dualMap-vs-rows prose drift in the argument.
8. Get an independent human or second-lens review of the manuscript lemma statement as revised, and of the whole-manuscript QA outside this scope.
9. Keep open: numeric NO; source/star/robust8S/pre-draw witnesses; sampler/encoded reduction/runtime/learning/upstream transports; R14 HIGH; warnings and fresh-checkout replay; novelty, citations and PDF; the final provider gate; and publication. **There is no overall GO.**
