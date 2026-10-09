# Proof-adversarial crosswalk review: finite spectral lemma, primary sources, Lean contract and actual callers

**This is not final acceptance.** I used no tools, wrote no files, and ran no Lean, Lake or subagents. I did not recompute any SHA-256; every hash below is copied from the packet headers. Everything here is informal source inspection, not kernel evidence. My acceptance scope is limited to the crosswalk between the spectral statement, the operators and the analytic callers. It does not cover the whole manuscript's validity or novelty.

## Verdicts

| Question | Verdict |
|---|---|
| **1. M1: does the source shape align?** | **Resolved.** The manuscript's finite-spectral lemma, the MZ v1 bilinear-scheme spectral lemma, MZ24 Lemmas A.10–A.13 and the Lean `Spectral47ExactContract` describe the same operators and sampling laws. The adjoint is restricted to an invariant first argument, normalization is squared, and the additive term is the same deliberately weaker bound. One citation and version item remains open (F7). |
| **2. Is the full exact argument mathematically sufficient?** | **Yes, informally.** The exact eigenvalue λ_i is our own reconstruction; MZ24 A.13 states only an upper bound. I re-derived it, and it implies every source bound and the unchanged contract inequality. I found no mathematical error. |
| **3. Is the actual consuming application complete?** | **Partial.** The frozen candidate discharges the Spectral47 premise of exactly one lemma: the old-namespace `selected_leaf_high_energy_le_spectral`. The complete SourceSize material caller and the dyadic caller still take `hSpectral` as an explicit hypothesis. |
| **4. Native and manuscript final readiness** | **Not ready.** The Full101 chain, the exact-energy candidate and the new wrapper plus its Checks file are all uncompiled. There is no overall GO. |

## 1. Coverage

**Read fresh and in full (the 8 new bodies):**
1. `paper/submission-manuscript.md` (6F8D…). I read all of it; my review focus is the finite-spectral lemma and its use in the inverse-agreement lemma.
2. `mz-v1 k_query_grassmann.tex` (1950…).
3. `mz24-v4 Fourier_appendix.tex` (A80A…).
4. `ActualFixedFunctionalBinaryMatrixMoment.lean` (87CC…).
5. `ActualSelectedComplementSourceSizeOriginalApplication.lean` (22DE…). This hash matches the Full100 native report's `source_sha256`.
6. `ActualSelectedComplementManuscriptDyadicMoment.lean` (AF3E…). This hash also matches the native report.
7. `ActualSelectedComplementSpectral47OriginalApplication.lean` (9261…).
8. `…Spectral47OriginalApplicationChecks.lean` (AA4F…).

**Also read as separate sections:** the current argument (76DF…, which adds the settlement and primary-source sections), the source-alignment audit (5229…), the root reconciliation and the three prior reports.

**The 33 earlier bodies were reused by identity, not freshly reviewed.** Their headers are claimed byte-identical to packet 7F2C…, which I cannot verify. I re-consulted only the declarations this crosswalk needs:
- `Spectral47ExactContract` in both namespaces;
- `selected_leaf_high_energy_le_spectral`, `selected_actual_material_moment_bound` and `SourceSizeContractBridge`;
- `spectral47_exact_contract_inhabitant`, `append_rank_projection_energy_le` and the `ExactImageEnergy` ratio;
- `frameProduct_ratio_le`, `frameProduct_zero_of_lt`, and the `pairing_mul_right`/`_transpose` orientations.

This review claims no fresh coverage of all 33 bodies or of the full 340-source capture.

## 2. Crosswalk

| Item | Manuscript | MZ v1 (bilinear spectral lemma) | MZ24 v4 (A.10–A.13) | Lean | Status |
|---|---|---|---|---|---|
| T | E_B F([X,B]), B unrestricted n×s | E over uniform columns v_i, appended on the right | Same | `appendAverage` = `uniformMean` over every `BinaryMatrix n s`; base columns first. `rawTF_eq_unconditional_binaryMatrix_mean` adds no rank condition | **Match** |
| 𝒢 | Uniform full-column-rank R ∈ F^{d×c} | Cites MZ24 | E[H(MA) \| rank A = c], with A of size 2ℓ×2(1−δ)ℓ | Not formalized | Shape matches; no native version |
| Φ | B unrestricted, C full row rank, independent | Same | Same | Not formalized | Shape matches; no native version |
| Adjoint | ⟨𝒯F,H⟩ = ⟨F,𝒢H⟩ for invariant F only; "no invariance of H" | Uses it with F^{=i} invariant | A.11 requires F to be basis invariant | Not formalized | **Match, restricted** |
| 𝒢𝒯 = Φ | Complete A = [R,A₂]; W = B − MA₂; C = last s rows of A⁻¹ | Cites A.12 | Same construction | Not formalized | Match |
| Eigenvalue | Exact: λ_S = Pr[SCᵀ = 0], equal to G(d−i,s)/G(d,s), which is 0 when s > d−i | Upper bound 2^{−i(2δℓ−1)} + 3·2^{i−n} | Upper bound 3q^{t−n} + q^{−t(2δℓ−1)} | Ratio G(c,i)/G(d,i) in an uncompiled candidate, by a different (fixed-image) route | **The exact value is a reconstruction**; it implies both source bounds |
| Normalization | Squared; unsquared contraction would be √λ | Squared | λ enters ⟨F,ΦF⟩ = ‖𝒯F‖² | Squared energies in the contract | **Match** |
| Additive term | Explicitly "the weaker bound used below" | Present | Present, from symmetrisation over random independent v | Kept in the contract | Match; the term is slack |
| Invariance | All M, all A ∈ GL(d,2) | Full-rank A | Full-rank A | `∀ M U V, UV = 1 → VU = 1 → F(MU) = F M` | Equivalent for square matrices over a field |
| Transpose | χ_S(MA) = χ_{SAᵀ}(M) | — | Lemma A.8 | `pairing(YUᵀ, M) = pairing(Y, MU)`; `pairing(YU, M) = pairing(Y, MUᵀ)` | Orientations consistent |

**Parameter mapping:**
- MZ ℓ ↔ Lean h; δ ↔ ρ; 2ℓ ↔ c+s = 2h; 2(1−δ)ℓ ↔ c; 2δℓ ↔ s.
- MZ's level d (or t in A.13) ↔ Lean i ≤ c+s.
- Ambient n = 2J in the Lean application (the side complement, via `sideComplement_finrank`). The manuscript uses the complement identity with n = 2J; MZ v1 uses F₂^U, with dimension 3J. This deviation is documented in the manuscript.
- The exponent −i(s−1) = −i(2ρh−1) matches MZ's −d(2δℓ−1).
- MZ's leaf count k ↔ Lean m ↔ the manuscript's m. Arity is m+1.

**Standing hypotheses:**
- MZ needs q = 2, an integral 2δℓ, and 0 ≤ d ≤ 2ℓ. Lean has all three.
- MZ's "sufficiently large ℓ" appears in Lean as `sourceHeightCutoff rho ≤ h`. Together with parity, ρ > 0 and the real c/s split, it is kept in the contract and unused by the proof. That is legitimate strengthening.

**Exact count re-derived.** pairing(S, BC) = ⟨SCᵀ, B⟩, so averaging over an unrestricted B leaves the indicator [SCᵀ = 0]. That condition says every row of C lies in the right kernel of S, which has dimension d−i, giving λ_i = G(d−i,s)/G(d,s).

MZ24 A.13 counts the zero minor using columns of A instead. That count is G(d−s,t)/G(d,t), and H-factorisation shows it is symmetric in s and t. All three expressions (MZ24's minor count, the kernel count, and the fixed-image ratio G(c,i)/G(d,i)) are equal.

Spot checks:
- (c, s, i) = (1, 1, 1) gives 1/3.
- (1, 1, 2) gives 0.
- i = 0 gives 1.

## 3. Findings

| # | Severity | Finding | Evidence | Disposition and action |
|---|---|---|---|---|
| **F1 (M1)** | was HIGH, now **resolved** | The manuscript T is the unconditional append; 𝒢 and Φ have exactly the source shape; the additive term is explained as slack. | Manuscript: the finite-spectral lemma's definitions, its proof, and the sentence "We retain that weaker form". MZ v1: the T definition and the spectral lemma. MZ24: the 𝒢 definition, A.11, A.12, A.13 | Close M1 as a statement- and operator-level crosswalk. Independent human review of the source PDFs is still open. |
| **F2** | MEDIUM (manuscript fidelity) | The manuscript states exact equality ‖𝒯F_i‖² = λ_i‖F_i‖². The sources give only an upper bound. The manuscript says "We reconstruct", which is correct attribution, but nothing native backs the equality. The Lean ratio route is a different proof from the manuscript's 𝒢/Φ/kernel route. | Manuscript proof; MZ24 A.13 "at most …" | Keep the equality labelled as a reconstruction. Either translate the 𝒢/Φ/adjoint/eigenvalue proof natively, or certify the ratio candidate plus a native product identity, and state in the crosswalk that Lean certifies the statement by a different proof. **Downstream use needs only the inequality**, so the native 𝒢/Φ debt is manuscript debt, not application debt. |
| **F3** | **HIGH (application scope)** | `Spectral47OriginalApplication` passes the inhabitant only to `ActualSelectedComplementAnalyticMoment.selected_leaf_high_energy_le_spectral`, in the old namespace. Three callers still keep `hSpectral : … Spectral47ExactContract …`: `SourceSizeOriginalApplication.selected_actual_material_moment_bound_original`, `ManuscriptDyadicMoment.selected_actual_material_moment_bound_original_at_dyadic_exponent`, and the old material bound. No supplied declaration composes `spectral47_contract_iff`. The old material bound takes `Instance N m`, which ties the source-row count to the leaf count; SourceSize uses `Instance N rows`. | Body of the candidate (imports and namespaces); the signatures of the SourceSize and dyadic files | Do not relabel the wrapper as completing the source table or runtime. Add SourceSize-namespace material and dyadic theorems that pass `(SourceSizeContractBridge.spectral47_contract_iff _).mp (spectral47_exact_contract_inhabitant _)`. They must keep `rows` independent, the same I/copies/U/A/C/T/f, fixed m, `original_HC46_exact`, and every height, parity, ρ, split and ambient guard. Never route through the old `Instance N m` material bound. Compile, then trace. |
| **F4** | LOW | The name `Spectral47ExactContract` means the exact *source shape*, not the exact eigenvalue. | Contract text | Document this so the inequality is not cited as the exact equality. |
| **F5** | MEDIUM (native) | Natural-number vs real zero cases. `frameProduct` uses truncated natural subtraction, but the product contains the j = k zero factor whenever i > k, so the natural and real values agree. In the λ product with i ≤ d, the j = d−i factor makes it zero when s > d−i; later real factors are negative but irrelevant. **But at s = 0 with i > d**, λ = 1 (empty product) while Lean's 0/0 = 0, so **λ_i = G(c,i)/G(d,i) needs i ≤ d**. The energies are 0 on both sides there. | `frameProduct_zero_of_lt`; real division convention | Any native ratio-to-product lemma must assume i ≤ d (the contract supplies i ≤ c+s) and take the explicit zero-factor branch, not rely on cast-pushing. |
| **F6** | LOW (resolved by typing) | Source notation slips, none inherited: (a) MZ24 A.11 says "G" in the statement where the proof uses H, and calls A⁻¹J a member of F^{n×2(1−δ)ℓ" when it should be 2ℓ×2(1−δ)ℓ; (b) MZ24 defines TH(M) but writes TF; (c) MZ24's completion uniformity is "clear", supplied here by the count ∏_{j=c}^{d−1}(2^d − 2^j); (d) MZ v1's high-part bound uses 3·2^{r−n} for i > r, although the term grows with i, and drops it; (e) MZ24 A.15 writes q^{−2dδℓ} instead of q^{−d(2δℓ−1)} and has an unstated large-n requirement in its √ step. | Source TeX | The typed reconstruction fixes (a)–(c). For (d), the manuscript correctly uses 2^{−(r+1)b} + 3·2^{2h−n} ≤ 2^{−rb} under n ≥ 2h + rb + log₂6; the Lean caller keeps per-level factors and is unaffected. (e) is outside A.10–A.13 and not consumed. |
| **F7** | MEDIUM (citation/QA) | Manuscript contract 4 cites "MZ24 revision 1"; the spectral citations are unversioned; the supplied file is v4. Counting v4 environments on a shared counter puts `lm: preserve pseudorandom` at A.17, while MZ v1 cites it as A.18. That suggests version drift; my count is uncertain from TeX labels alone. The same count on MZ v1 reproduces the manuscript's 4.2, 4.5, 4.6 and 4.7. | Labels in both files | Pin one MZ24 version and check numbers against its PDF before citing A.10–A.13 or A.17–A.18. |
| **F8** | LOW | Symbol collisions in the argument: G(k,i) is both the frame count and the operator 𝒢; H(t) is both the product and the test function; T is both the manuscript's Hölder exponent and the operator 𝒯; k means leaf count in MZ and the moment exponent in Lean. | Argument text | Rename (for example `frameProduct` and `Hprod`) in any manuscript or crosswalk text. |
| **F9** | **HIGH (open, pre-existing)** | Premises still open downstream even once spectral is discharged: `hsel`, `hA`, `hrd`, `hfail`, `a > 0`, k dyadic with k ≥ 4m. The scalar steps are not formalized: collapsing the analytic right-hand side, the high part ≤ 2^{−rb}, choosing T and P, the signal contradiction, and robust local decoding. The dyadic caller allows k = P ≥ mT ≥ 4m, and its β^{1−m/k} ≤ β^{1−1/T} is consistent with the manuscript, but this lies outside the spectral scope. | SourceSize and dyadic bodies; the manuscript's inverse lemma | Keep open; formalize separately. |
| **F10** | **HIGH (native)** | The 11 Full101 bodies, the ExactImageEnergy candidate and its Checks, and the new wrapper and its Checks are uncompiled. Elaboration risks: the wrapper opens several namespaces (`MatrixLiftNominalDirectComparison` is unsupplied), so name ambiguity is possible; the inhabitant and the empty-fibre lemma may raise unused-binder warnings; the earlier A1 instance, cast and HEq risks remain. | Status labels | Run GCP compilation with the unchanged gates, collect axiom profiles, then do the consumption trace. Do not preemptively edit the frozen bytes. |
| **F11** | MEDIUM | Unsupplied prerequisites that affect this scope (see §4). | — | Supply them for review. |
| **F12** | LOW | The argument's prose counts via duality; Lean counts via independent rows. | Argument vs `BinarySurjectionCounting` | Correct the prose. |

**Actual caller checks (all passed):**
- `ActualFixedFunctionalBinaryMatrixMoment` sends array column j to matrix column j, which agrees with "base first" append ordering.
- The append average is unconditional.
- One common base is shared across the k independent draws.
- The factor 2 comes from the rank-failure bound (c + ks)·2^{c+s−1}/2^n ≤ 1/2. This is at least as weak as the manuscript's (2h + 2ρmh)·2^{2h−n} ≤ 1/2.
- The low levels use the ordinary L^p contraction (Jensen); only the high levels use the squared spectral bound. No Lean statement uses √λ.

## 4. Unsupplied prerequisites that affect this scope

- **Project modules:**
  - `ActualBinaryMatrixHC46OriginalExactInhabitant` (`original_HC46_exact`; its axiom profile is not shown here);
  - `ActualSelectedComplementSourceSizeAppendMoment` and the old `ActualSelectedComplementAppendMoment`;
  - `ActualSelectedSpectralParameters` (`selected_spectral_parameters`, `analyticSourceHeightFloor`, `leaf_split_total`);
  - `ActualRankImageRightBasisInvariance`, `ActualLeafLabelRankImageAlignment`, `ActualFiniteMomentLpBounds`;
  - `ActualFixedFunctionalStarMoment`, the `MatrixGrassmann{Identity,Moment}` modules, `MatrixLiftNominal{DirectComparison,Domain}`;
  - `ActualComplementCoordinateMassBridge`, the `ActualTagged*` modules, `ActualCmmsa{AdmissibilitySelector,ParameterReconciliation}`;
  - `ActualStarFixedRhoDimensionGuard`, `SamplerParameters`, `ActualOrdinaryStarWeightedSelection`, `ActualMaximalPairLadder`, `ActualSourceStarLaw`, `ActualBinaryGrassmannSamplingBounds`.
- **Mathlib:** `MeanInequalities` (the weighted Hölder lemma), `Matrix/Basis`, `Dual/Basis`, and the bodies of `equiv_linearIndependent` and `card_compl_set`.
- **Primary sources:**
  - MZ v1 Definition 2.1 and the bilinear pseudorandomness definition;
  - the level-d decomposition equation;
  - MZ24 main-text Lemma 5.x and the A.14–A.18 consumers;
  - Evra–Kindler–Lifshitz theorems;
  - compiled PDFs or `.aux` files to confirm numbering;
  - the "fresh source custody" document.

## 5. Remaining to-do list

1. Renew GCP authentication. Compile frozen Full101, the ExactImageEnergy candidate and its Checks, and the Spectral47OriginalApplication wrapper and its Checks under the unchanged gates. Collect axiom profiles and warning diagnostics.
2. Add and compile SourceSize-namespace material and dyadic theorems that discharge `hSpectral` through `spectral47_contract_iff`, keeping `rows`, the common I/copies/U/A/C/T/f, fixed m, `original_HC46_exact` and every guard. Then trace actual consumption (F3).
3. Get native evidence for the recovered covariance and orbit duplicates, or consume the Full100 declarations directly.
4. Either translate the native product identity (assuming i ≤ d, with the zero branch) together with the 𝒢/Φ, completion marginals, adjoint and kernel eigenvalue, or explicitly scope the manuscript equality as a prose reconstruction (F2, F5).
5. Pin the MZ24 version and verify all cited numbers (F7). Fix the symbol collisions and the duality prose (F8, F12).
6. Supply the bodies listed in §4 for independent review. Get independent human review of the manuscript against the source PDFs.
7. Formalize the downstream scalar steps: high part ≤ 2^{−rb}, the T/P choice, the signal contradiction, and robust local decoding (F9).
8. Keep these open: numeric NO; source, star, robust8S and pre-draw witnesses; physical sampling; encoded selection, reduction, runtime and learning; upstream transports; R14 HIGH; warnings and fresh-checkout certification; novelty, citations and PDF; the provider gate and final QA; publication. **No overall GO.**
