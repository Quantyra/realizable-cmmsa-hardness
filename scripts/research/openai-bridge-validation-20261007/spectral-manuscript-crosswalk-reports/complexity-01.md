# Complexity review: spectral manuscript, primary-source and actual-caller crosswalk

**This is not final acceptance.** I used no tools, file writes, Lean/Lake or subagents, and I recomputed no hashes. Every hash and status below is copied from the packet. This is an informal reading of the sources, not kernel evidence.

The acceptance scope is limited to the spectral statement, the operator and the analytic callers. It does not cover full manuscript validity, novelty, citations or publication.

## Verdicts

| Question | Verdict |
|---|---|
| **M1: does the source shape match?** | **Yes, at the informal level.** The unconditional T, the uniform-injection G, Φ with unrestricted B independent of full-row-rank C, the restricted adjoint, the squared normalization and the parameter mapping all agree across: the manuscript lemma, MZ v1 Section 4.2 / Lemma 4.7, MZ24 A.10–A.13, and the Lean contract. The exact eigenvalue and the exact energy equality are our own reconstruction. A.13 only gives the weaker bound with the 3·q^(t−n) term. Two residual items remain: a wording fix (F4) and the missing typed Lean definitions of G, Φ and the adjoint (F3). |
| **Is the full exact argument sufficient?** | **Yes.** I found no mathematical error. I checked every zero and empty case, both transposes, the squared versus ordinary contraction, and the natural-number versus real conversion. |
| **Does an actual caller consume the result?** | **No.** The frozen candidate discharges `hSpectral` in exactly one place: the legacy-namespace high-energy wrapper. It is not consumed by the SourceSize material caller, the original-HC46 caller, or the dyadic caller (F1, F2). |
| **Native and manuscript readiness** | **Not ready.** Full101, the exact-energy candidate and the new application are uncompiled. GCP authentication is pending. No overall GO. |

## 1. Coverage

**Freshly reviewed in full:** the 8 new bodies below.

1. `paper/submission-manuscript.md` (6F8D6534…). I read it in full. For acceptance, only the finite-spectral lemma and the inverse-agreement caller are in scope.
2. MZ v1 `k_query_grassmann.tex` (19503AA3…).
3. MZ24 v4 `Fourier_appendix.tex` (A80A78BF…).
4. `ActualFixedFunctionalBinaryMatrixMoment.lean` (87CC5C41…). This is the module that defines the coordinate equivalence.
5. `ActualSelectedComplementSourceSizeOriginalApplication.lean` (22DE415F…).
6. `ActualSelectedComplementManuscriptDyadicMoment.lean` (AF3E380A…).
7. `ActualSelectedComplementSpectral47OriginalApplication.lean` (9261DEA4…).
8. Its Checks file (AA4F9E0F…).

I also read two separate sections: the source-alignment audit (52295A1A…) and the current argument (76DF5E79…).

**Reused, not re-reviewed:** the 33 earlier bodies, the native report, the earlier argument, the three earlier reports and the reconciliation. They were supplied again and are said to be byte-identical (packet 7F2CAE47…). I used their contents as stated and did not re-derive them. This review does not claim fresh coverage of all 340 sources or the 327-source closure.

**Hashes cross-checked against the Full100 native report:** bodies 5 and 6 match the native-qualified source hashes listed there. Body 4 is not in the added list. I assume it is in the 327 Full100 closure but cannot verify that. Bodies 7 and 8 are new and uncompiled.

## 2. Crosswalk table

Notation clash to keep in mind: in MZ, *d* means the Fourier level. Here d means c+s and i means the level.

| Item | Manuscript | MZ v1 / MZ24 | Lean | Result |
|---|---|---|---|---|
| T | E_B F([X,B]), B uniform over all n×s | `T F(M)=E_v F([M,v_1..v_{2δℓ}])` | `appendAverage`: base columns first (`finSumFinEquiv`), B is `uniformMean` over all n×s | Match. The coordinate equivalence `fun i j => A j i` sends array column j to matrix column j, so the orientation of [X,B] is preserved. |
| G | Average over full-column-rank d×c R of H(MR) | MZ24 A.11: E_A[H(MA) \| rank A = 2(1−δ)ℓ] | **No definition** | Shape matches. No Lean object exists. |
| Φ | B unrestricted n×s, independent of C (s×d, rank s) | MZ24 A.12: B = [w_1..] is independent of R, and C is the last rows of R⁻¹ | **No definition** | Match. MZ24 gets independence directly from w being independent of R. Our proof uses the translation B ↦ B − MS. The two are equivalent, since uniform w absorbs MR″. |
| Adjoint | Restricted to an invariant first argument; no invariance of H needed | A.11 (needs invariant F) | None | Match. No unrestricted adjoint is claimed anywhere. |
| Eigenvalue | λ_S = Pr[S Cᵀ = 0]; exact product formula, 0 when s > d−i | A.13: a bound only, \|λ\| ≤ 3q^(t−n) + q^(−t(2δℓ−1)) | None (Full101 proves λ ≤ 2^(−is)) | The exact formula is **reconstruction, not quotation**. Transpose checked: tr(Sᵀ B C) = ⟨S Cᵀ, B⟩, and the rows of C lie in ker S, of dimension d−i. |
| Normalization | Normalized L², squared, "unsquared would be √λ" | MZ v1 Lemma 4.7 is squared | Contract compares `uniformMean (·)^2` on both sides | Squared on every side. The low-part Lp contraction (Jensen, factor 1) is a separate fact and is used correctly. |
| Parameters | s = s₀ = 2ρh, c = t₀ = 2(1−ρ)h, d = 2h, n = 2J, b = s₀ − 1 | s = 2δℓ, d = 2ℓ, q = 2, ρ ↔ δ, h ↔ ℓ | `hEven`, `hc`, `hs`, `hHeight`, n := 2·J | Match. The concrete value J = `blocks samplerA h` versus the manuscript's J = 2^(2^(Ah²)) cannot be checked, because SamplerParameters was not supplied. |
| Invariance | F(MA) = F(M) for every A in GL(d,2) | Basis invariance | U·V = V·U = 1 for all M | Equivalent over a finite field. Lean is real-valued; MZ allows complex values. Real is enough for the indicator callers. |

**How the typed reconstruction handles the source notation**

- **Resolved.** MZ24 A.11 states the adjoint with G on one side and H on the other, and writes the dimension of A⁻¹J as n×2(1−δ)ℓ where it should be 2ℓ×2(1−δ)ℓ. MZ24 A.15 uses H and G interchangeably. The manuscript's typed statement fixes all of these: G maps n×c functions to n×d functions, and the second argument is unrestricted.
- **Still open in Lean.** That typing exists only in prose. No `def` for G or Φ exists.
- **Overloaded symbols in the manuscript (F7).** G is used both for the center indicator and for the operator 𝒢. d is used both as the MZ level and as our c+s.
- **Left as-is (out of scope, not repaired).** Two typos in MZ v1 that lie outside the spectral scope: "codim(Q)+dim(W)" in its consistency theorem, and E_f μ(S_{R,f}) = 2^(−2ℓ(1−1000δ)). The manuscript uses dim Q + codim W correctly.

## 3. Findings

| ID | Severity | Body evidence | Disposition and action |
|---|---|---|---|
| **F1: application not consumed** | **HIGH** (consumption) | The Spectral47 application only applies the legacy `selected_leaf_high_energy_le_spectral … (spectral47_exact_contract_inhabitant _)`. The SourceSize `…material_moment_bound_original` and both dyadic theorems still take `(hSpectral : Spectral47ExactContract sourceHeightCutoff)` as an explicit premise. | **Open.** This is a selected-leaf wrapper. It is not completion of the material, source, table or runtime chains. **Action:** add SourceSize callers that pass `(SourceSizeContractBridge.spectral47_contract_iff c).mp (spectral47_exact_contract_inhabitant c)` into the material caller and the original-at-dyadic caller, keeping every other premise. Then compile them and trace. |
| **F2: namespace and lane mismatch** | **MEDIUM** | The application imports the **legacy** `ActualSelectedComplementAnalyticMoment`. In that module the material caller is `Instance N m`: the source-row count is tied to the arity m. The SourceSize module uses an independent `rows`. The wrapper's conclusion is stated with legacy `selectedHigh`, `selectedF` and `selectedHighFinIndexSet`, which are different constants from the SourceSize copies (same bodies, different names). | **Open.** Do not wire the inhabitant into the legacy material caller. Bridge through the contract `Iff.rfl`, not through the legacy wrapper. If a wrapper-level result is needed, add explicit definitional-equality lemmas for the selected* constants. |
| F3: exact operator laws missing from Lean | **HIGH** (native) | No Lean source for: the λ product identity, 𝒢, Φ, the completion marginals, Φχ = λχ, the restricted adjoint, or the operator-route energy. The exact-energy candidate gives only the frame-product ratio, and it is uncompiled. | Kept from earlier review (N1). The manuscript states equality and λ_i; the Lean contract encodes only the weaker bound. |
| F4: attribution wording | **MEDIUM** (non-claims) | The manuscript says it reconstructs "the calculation behind MZ Lemma 4.7 and MZ24 Lemmas A.10–A.13" and then states the exact λ_i. A.13 contains only an upper bound. | **Action:** add one sentence saying A.13 gives only the bound with the 3q^(t−n) term. The exact kernel-frame value is a direct finite reconstruction, with no novelty claimed. |
| F5: source slack | LOW (information) | MZ v1 bounds the high levels with the level-r factor 3·2^(r−n), but 3·2^(i−n) grows with i. The manuscript uses 3·2^(2h−n), which is correct. The exact λ_i ≤ 2^(−is) decreases with i, so the issue disappears. | Not a defect in our route. Record it. |
| F6: natural vs real zero factor | LOW | `frameProduct` subtracts in ℕ and handles i > c through the j = c zero factor. The real manuscript product needs i ≤ d (the contract supplies `hi`) and the explicit branch s > d−i. | Correct as stated. The real conversion lemma is still to be written, and it must keep that branch. |
| F7: notation overloading | LOW | G (indicator vs operator); d (level vs width); MZ's t is the level in A.13. | Put a symbol table in the crosswalk. |
| F8: missing imports | **MEDIUM** | `original_HC46_exact` (body of `ActualBinaryMatrixHC46OriginalExactInhabitant`); `ActualSelectedSpectralParameters` (supplies hsplit, hcReal, hsReal, hcutFloor); `ActualSelectedComplementSourceSizeAppendMoment` (discharges `hsmall`); `MatrixGrassmannIdentity`; `ActualFixedFunctionalStarMoment`; `ActualRankImageRightBasisInvariance`; `ActualLeafLabelRankImageAlignment`; `SamplerParameters`; Full101 bodies not resupplied. | These affect guard provenance and HC46 consumption. They need body review. |
| F9: stale banners | LOW | Bodies 5 and 6 still carry "uncompiled candidate" banners, but their hashes match Full100 native-qualified entries. | The report is authoritative. Keep the bytes as historical. |
| F10: axiom checks | LOW | The Checks file prints axioms only for the application theorem. | Also print axioms for `spectral47_exact_contract_inhabitant`, the exact-energy theorems, and every future SourceSize consumer. |
| F11: ambient conditions | INFO | The manuscript's inverse-lemma lower bounds on n, and its rank-failure condition (d + ms)·2^(d−n) ≤ 1/2, do not appear in the Lean callers. Lean uses `hsmall` with (c + ks)·2^(d−1)/2ⁿ ≤ 1/2, which is a weaker requirement and compatible. Its discharge is in an unsupplied module. The Lean callers stop at `selected_actual_analytic_rhs`; the inverse contradiction is not formalized. | This is downstream and numeric. Keep it open. |

## 4. What the actual callers retain

| Item | Status |
|---|---|
| Spectral premises the frozen candidate actually removes | Only `hSpectral` inside the legacy `selected_leaf_high_energy_le_spectral` wrapper, and only once the candidate compiles. |
| Premises that remain in the SourceSize original and dyadic callers | `hSpectral`; `hsel` (selector); `hA : 1 ≤ samplerA`; `r`, `hrd`; `e ≥ 0`; `hfail` (failed-zoom on the coordinate leaf table); `a > 0`; for dyadic, also `hkDyadic` and `4m ≤ k`. |
| HC46 | Discharged in both callers by `original_HC46_exact`, which is native-qualified. Its body was not supplied. |
| Preserved correctly | The shared I/copies/U/A/C/T/f across mass, center identity, PR and moment. Separate `rows` (SourceSize). Fixed m (moment arity = number of leaves). Source height, parity, ρ and the c/s split, all from `selected_spectral_parameters`. `hdim : c+s ≤ n` from h² < J. The dyadic exponent window matches the manuscript's P ≥ mT ≥ 4m. |
| Complexity | Every step is finite existence and counting with classical choice. There is no sampler, no encoded witness, no runtime, no reduction and no learning procedure. Spectral completeness implies no hardness and no numeric NO. |

## Remaining to-do list

1. Renew GCP authentication. Natively compile the frozen Full101 (unchanged), the exact-energy candidate and Checks, and the Spectral47 application and Checks. Collect real diagnostics before any warning repair.
2. Fix F1: add SourceSize material, original-HC46 and dyadic callers that discharge `hSpectral` through `spectral47_contract_iff`. Keep every other premise and the `rows`/m separation. Compile them, print axioms, and trace consumption.
3. Do not use legacy-lane wiring (F2). If wrapper-level reuse is needed, add definitional-equality lemmas for the selected* constants.
4. Translate the real λ product identity, keeping the i ≤ d guard and the s > d−i zero branch. Define 𝒢 and Φ in Lean. Prove the completion marginals, 𝒢T = Φ with independent unrestricted B, Φχ = λχ, the restricted adjoint, and exact energy. Get independent native-body review.
5. Fix the manuscript wording (F4) and add a symbol table (F7). Record the MZ v1 level-slack observation (F5) and the MZ24 notation typos.
6. Supply and review the import bodies listed in F8, and the downstream discharge of `hsmall` and the ambient guards (F11).
7. Extend the axiom checks (F10). Keep the stale banners as historical bytes (F9).
8. These stay open: numeric NO, source/star/robust8S/pre-draw witnesses, sampling, encoded selection/reduction/runtime/learning, upstream transports, R14 HIGH, warnings and fresh-checkout custody/replay, novelty/citations/PDF, final provider and QA, publication. **No overall GO.**
