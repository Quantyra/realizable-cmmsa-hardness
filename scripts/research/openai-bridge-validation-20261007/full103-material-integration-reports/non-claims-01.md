# Non-claims review: Full103 conditional integration of Full340/Full251/Focused83 (spectral repair)

## Verdicts

| Scope | Verdict |
|---|---|
| **Mathematical soundness of the 13 fresh bodies** | **Sound.** I found no soundness, orientation, quantifier, normalization or vacuity defect. |
| **Native translation of the universal Spectral47 contract** | **Achieved for exactly the stated contract.** `spectral47_exact_contract_inhabitant` inhabits the unchanged, guarded Spectral47 contract with the weaker `+3` term, for every cutoff. Standard axiom profile, per the receipt. |
| **Native application to the legacy selected leaf** | **Achieved for one lemma only.** `selected_leaf_high_energy_le_spectral_original_application` discharges the spectral premise of the legacy high-energy leaf lemma. It does not discharge it in any material export. |
| **Conditional integration with SourceSize, HC46 and dyadic** | **GO-WITH-NOTES, still conditional.** Every SourceSize, dyadic, legacy-material and HC46-original export still takes `hSpectral` as a premise. Those bytes are unchanged from Full95/97. |
| **Overall GO** | **Not issued.** Two HIGH findings are open: F1 (the material consumers still take `hSpectral`) and R14 (encoded reduction and runtime). Many other full-scope gates are also open. |
| **Manuscript, publication, novelty, priority** | **No acceptance requested, none given.** |

How I worked: I used no tools, wrote nothing, and ran no Lean, Lake or subagents. I recomputed no hashes. Every hash check below is a string comparison of values in the packet. Native, trace, custody and reuse facts are taken from the receipts.

## 1. Coverage: what I read fresh and what is inherited

**Fresh, read line by line, every declaration (13 bodies).** Every header SHA matches the native `source_sha256`:

| Module | Header SHA matches source SHA? |
|---|---|
| `ActualFiniteBinarySurjectionCounting` (BA136FC5) | yes |
| `ActualFiniteBinaryImageFibres` (0C1610A6) | yes |
| `ActualFiniteBinaryImageOrbit` (C5670FFE) | yes |
| `ActualFiniteBinaryImageOrbitFourier` (10A87647) | yes |
| `ActualFiniteAppendSpectral47` (371FD673) | yes |
| `ActualFiniteAppendImageWeighted` (861C5677) | yes |
| `ActualFiniteFrameProductRatio` (92072C90) | yes |
| `ActualFiniteAppendImagePerImageEnergy` (56D96C2C) | yes |
| `ActualFiniteAppendImageTailBridge` (4A22102D) | yes |
| `ActualFiniteAppendGlobalImageEnergy` (2B2A6AFB) | yes |
| `ActualFiniteAppendSpectral47ExactInhabitant` (2F8A6758) | yes |
| `ActualSelectedComplementSpectral47OriginalApplication` (9261DEA4) | yes |
| `…OriginalApplicationChecks` (AA4F9E0F; only `#check` and `#print axioms`) | yes |

**Integration interfaces in the 75 parent bodies, re-checked fresh in this pass:**
- The four SourceSize/dyadic bodies. Header SHAs (D4B86B56, 03FB0A5D, 22DE415F, AF3E380A) match the typed `source_sha256` values.
- `SourceSizeContractBridge`, `BinaryMatrixSameRangeOrbit`, `BinaryMatrixRightOrbit` and `BinaryMatrixRightFourierCovariance`. Headers match.
- `MatrixLiftAffineTarget` (`surjective_target_orbit`).
- Legacy `ActualSelectedComplementAnalyticMoment`: `Spectral47ExactContract`, `selected_leaf_high_energy_le_spectral` and `appendHighLevel_energy_le_spectral_sum`.
- `ActualAppendFourierCrossLevelOrthogonality`: `appendAverage_character`, `character_appendBinaryMatrix` and the castAdd/natAdd orientation.
- `ActualFixedFunctionalAppendOperator`: append order, `appendBinaryMatrix_columns`.
- `ActualRankImageRightBasisInvariance`.
- Mathlib `Rank`, `ToLin` and `Finiteness`.

**Inherited, not re-derived in this pass:**
- The other supplied parent bodies: the 23 Complexitylib modules, the reached tagged/star/Cmmsa/occurrence modules, the HC46 inhabitant and the remaining critical files.
- These are byte-identical under the reuse audit (`changed_prior_bodies` empty, 8084 shared constants and edges). I checked them against the preserved findings but did not re-derive them.
- This is identity reuse. It is not a fresh reread of all 340 bodies and not a fresh-checkout object replay.

**Not supplied in this packet:**
- `BinaryMatrixFourier`. Its body was reviewed in the Full100 addendum; its source identity remains Low residual ID-F2.
- `GrassmannCounting`, which defines `frameProduct`, `Frame` and `card_frame`. Its definitions are consistent with every use I saw: `frameProduct n a = ∏_{j<a}(2^n − 2^j)`.
- `Data/Matrix/Diagonal`.
- The other unsupplied members of the 340-body and 411-external corpus. Availability is not review.

**Skipped required fresh bodies: none.**

## 2. Declaration audit of the fresh bodies

### Counting (SurjectionCounting, ImageFibres)

- **`matrix_surjective_iff_rows_independent`.** Surjective ⇔ rank = i (range finrank against codomain dimension i) ⇔ rows independent (`rank_matrix` and `rank_eq_finrank_span_row`). Correct for any i and d.
- **`surjectiveMatrixFrameEquiv` and `card_surjective_coordinate_maps`.** The i rows of an i×d matrix form an independent frame in a d-dimensional space, so the count is `frameProduct d i`.
  - The i > d branch is handled two ways, and they agree: `fintype_card_le_finrank` makes the frame type empty, and the product has the zero factor j = d.
  - The argument uses independent rows directly, not biduality. That is the simplification the reviewers recommended.
- **`linearMapCoordinateEquiv`.** Both inverse laws are proved, and surjectivity transfers in both directions.
- **`matrixImageFibreEquivSurjections`.** Codomain restriction to the fixed image E, with inverse `toLin'.symm (E.subtype ∘ f)`. Both inverse laws are proved. Rank equals `hE` because `range(E.subtype ∘ f) = E`.
- **`card_matrixImageFibre = frameProduct d i`.** This requires `finrank E = i` as an explicit premise. That is correct: no count is claimed for a mismatched E.
- **`appendDomainEquiv`, the left projection and right injection, `appendedZeroSurjectionEquiv`.**
  - Base coordinates come first, matching the order in `appendBinaryMatrixEquiv`.
  - A map is retained exactly when it kills the right summand.
  - The equivalence to surjections from `Coord c` is proved in both directions, using `appendDomain_decomposition`.
  - The count is `frameProduct c (finrank E)`.

### Orbit and Fourier constancy (ImageOrbit, OrbitFourier)

- **`exists_domain_equiv_of_surjective`.** Kernel-plus-codomain splitting with equal kernel finrank, so g ∘ U = f. Correct, and it covers deficient and zero cases.
- **`exists_right_action_same_image`.**
  - Both inverse laws `U*V = 1` and `V*U = 1` are proved through `mulVecLin_mul`.
  - The orientation `B*U = A` is the domain right action.
- **`fourierCoeff_rankProjection_eq_same_image`.**
  - It applies `fourierCoeff_mul_right_transpose_eq` with W = Uᵀ, so `B*Wᵀ = B*U = A`. The transpose orientation is correct.
  - Basis invariance of `rankProjection i F` comes from `rankProjection_mul_right_eq`.
  - Constancy is asserted only within a fixed E, never across images.

### Actual append operator (Spectral47)

- **`pairing_mul_right_transpose`.** The direction is `pairing(Y·Uᵀ, M) = pairing(Y, M·U)`, via trace cyclicity. This is consistent with `pairing_mul_right` in `RightFourierCovariance`, which has the mirror orientation.
- **`rank_mul_right_transpose_eq` and `rankProjection_mul_right_eq`.** These hold for every real F, not only Booleans. This is the MZ24 A.10 analogue.
- **`appendAverage_character_pair`.** This is the unconditional pair correlation. It equals 1 exactly when the frequencies coincide and the tail is zero. All four tail cases are handled.
- **`appendAverage_rankProjection_energy_eq`.** E_M[(A_s P_i F)²] = Σ_{rank Z = i, tail Z = 0} F̂(Z)².
  - Each carrier is normalized by its own size, so no stray factor appears.
  - Nothing is conditioned on rank, and no Booleanity is assumed.

### Weighting and ratio (ImageWeighted, FrameProductRatio, PerImageEnergy)

- **`retainedMatrixImageFibreEquiv` and `card_retainedMatrixImageFibre = frameProduct c i`.** This is a fibrewise equivalence for a fixed E.
- **`frameProduct_scaled_le` (i ≤ c).** I checked it factor by factor: 2^s(2^c − 2^j) ≤ 2^{c+s} − 2^j. The natural-number subtraction is safe because 2^j ≤ 2^c.
- **`frameProduct_scaled_le_all`.** For i > c the left side is zero, through `frameProduct_zero_of_lt`.
- **`frameProduct_ratio_le`.** G(c,i)/G(c+s,i) ≤ 2^{−is} for every i.
  - The natural-to-real conversion is correct: no factor truncates when i ≤ c, and the zero branch is explicit when i > c.
  - For i > c+s Lean evaluates 0/0 as 0, which is a vacuous instance. Downstream consumers carry `hi : i ≤ c+s`, so they never rely on that case (Info).
- **`per_image_fourier_energy_ratio`.** Retained and full sums each factor as count × coefficient², at one representative of the same image. Then G(c,i)·a² ≤ 2^{−is}·G(c+s,i)·a², using a positive denominator from `hi`.

### Tail bridge and globalization (TailBridge, GlobalImageEnergy)

- **`appendRightInjection_single`, `appendBinaryMatrix_mulVecLin_comp_right` and `appendMatrix_tail_comp_zero_iff`.** A single right-summand vector maps to the natAdd column, which is the W block. The tail kills the map exactly when W = 0. Orientation is consistent with castAdd/natAdd.
- **`retained_iff_appendedFrequencyPart_zero`.** The retained surjection predicate is exactly the spectral zero-tail predicate.
- **`rankMatrixImageEquivSigma`, `sum_rank_matrices_by_image` and `sum_retained_matrices_by_image`.** Exact finite partitions by actual range. The `cast` transport lemmas are confined to sigma extensionality.
- **`per_image_energy_ratio`.** If the fibre is empty, both sides are empty sums and no representative is chosen. If it is nonempty, a witness is extracted.
- **`rank_i_retained_energy_le` and `append_rank_projection_energy_le`.**
  - The constant 2^{−is} is pulled out of a sum over images.
  - No coefficient of one image is compared with a coefficient of another image.

### Inhabitant and application

- **`rankProjection_parseval_restricted_eq`.** Parseval applied to P_i F, with the coefficient filter. Correct.
- **`append_dyadic_factor_le_spectral_factor`.** −is ≤ −i(s−1) because i ≥ 0. This includes s = 0 and i = 0.
- **`spectral47_exact_contract_inhabitant`.**
  - It intros every binder of the legacy contract (hEven, hi, hRho, hc, hs, hHeight) and uses only `hi`. All guards remain in the statement; none is deleted.
  - The `3·2^{i−n}` term is used only for its nonnegativity.
  - F is an arbitrary real function. The hypothesis `basisInv` covers all matrices and paired inverses.
  - n < i is allowed: both sides are then empty sums.
- **`selected_leaf_high_energy_le_spectral_original_application`.** Its binders and the call match legacy `selected_leaf_high_energy_le_spectral` exactly. It supplies the inhabitant at the caller's `sourceHeightCutoff`, retains hEven, hRho, hc, hs and hHeight, and keeps the same `selectedF T f` leaf.

## 3. Findings

| ID | Severity | Declaration / location | Evidence | Disposition and action |
|---|---|---|---|---|
| F1 (carried) | **HIGH (native integration)** | SourceSize `selected_actual_material_moment_bound[_original]`, both dyadic exports, legacy material exports | Each still binds `hSpectral : Spectral47ExactContract`. The inhabitant is typed against the legacy constant; the SourceSize constant needs `spectral47_contract_iff`, which is `Iff.rfl`. That composition is not in Full103, and Full104 is frozen and outside scope. | Mathematically a one-step transport, but not natively consumed. Keep HIGH until a discharged export is natively qualified, traced and reviewed. |
| N103-1 | Verified | All counting, orbit, energy and ratio declarations above | §2 | None. |
| N103-2 | Info (non-claim) | `spectral47_exact_contract_inhabitant` | It proves the inequality ≤ 2^{−is}·energy, which is stronger than the contract. | It does not prove the exact projected-energy equality, the s-factor eigenvalue, the G/Phi identities, the restricted adjoint or the cross-level manuscript equality. Do not cite it for those. |
| N103-3 | Medium (fidelity, carried FID-1) | Contract versus manuscript Lemma 4.7 and MZ24 A.13 | The source guards and the +3 slack are unused. | The bound is a separate reconstruction. Do not present it as the literal statement of A.13. No counting or Fourier novelty is claimed. |
| N103-4 | Low (hygiene) | `ActualFiniteBinaryImageOrbit` and `…OrbitFourier` | These duplicate `surjective_target_orbit` and `RightFourierCovariance` in substance. | Each has its own native evidence. Consolidate later. |
| N103-5 | Low (stale text) | `Spectral47OriginalApplication` docstring ("candidate pending authoritative GCP kernel/axiom verification"), the RightOrbit header, the "has not been compiled" headers in the SourceSize/legacy OriginalApplication files and the dyadic file | Contradicted by the native receipt. | No evidential weight either way. Clean up before render. |
| N103-6 | Low (receipt labels) | Native JSON | It reports `universal_Spectral47_inhabitant_proven: false` next to `_native_verified: true`. `material_body_review_complete` and `consumption_trace_complete` are false; these are historical. | Rename or clarify the flags. |
| N103-7 | Info | Unused guard binders in the inhabitant | The receipt reports zero owned warning headers. I did not verify the linter configuration independently. | Leave the inherited warning gate open. |
| N103-8 | Info (evidence tier) | "687 compiled objects" | This figure does not appear in the supplied native JSON, which shows 566 unchanged. | Receipt tier only. Reconcile during replay. |
| N103-9 | Info | Checks file | Its `#print axioms` output is build-log information, not evidence. | Warning and log disposition. |
| R14 (carried) | **HIGH** | Encoded reduction and runtime | No runtime theorem covers the doubly exponential J. | Bars overall GO. |
| Carried, unchanged | Medium/Low | Numeric NO (`hfail`, useful e, a), joint source/selector/copies/U/A witness, source/star/robust8S, pre-draw table, sampler, upstream transports, fresh checkout, inherited warnings, `BinaryMatrixFourier` source identity, stale banners, legacy coupling of m to the row count | — | Preserved. |

## 4. Integration checks (re-confirmed against unchanged bytes)

- **Row count and arity.** `Instance N rows` keeps the source row count independent of the leaf arity m.
- **One set of objects.** The same I, copies, U, A, C, T and f are used throughout. One `Tc` serves `hfail`, the PR premise and the moment. `Cc` and `fc` are used in the center identity.
- **Dimensions.** c + s = 2h ≤ 2J. `hdim`, `hD` and `hsmall` are derived. `hrd : r < c+s` and `1 ≤ samplerA` are retained.
- **HC46.** It is discharged through `original_HC46_exact` with `hEven := hsplit`.
- **Dyadic exponent.** The caller chooses a dyadic k ≥ 4m.
- **Selector and table guards.** The selector floor, failed-zoom, source-height and rank guards are unchanged.
- **No substitutions.** The append experiment is not replaced by uniform or rank-one noise. The source/star family is not narrowed. No fixed exponent below mT is introduced.
- **Native spectral evidence covers only:** the universal contract, and the legacy high-energy leaf lemma. It does not cover any material conclusion.

## 5. Separation of status

- **Mathematics.** The fixed-image counting/orbit/energy route to the guarded Spectral47 inequality is sound. The exact operator route (eigenvalue, G/Phi, adjoint) remains a reviewed argument only.
- **Native translation.** The universal inequality contract and the legacy leaf application have standard profiles. No exact eigenvalue, G/Phi, restricted-adjoint or cross-level equality has native evidence.
- **Conditional integration.** The material exports remain conditional on `hSpectral` (F1).
- **Overall readiness.** Not ready, because of F1, R14 and the other open gates.

## Remaining to-do

1. **F1.** Build and natively qualify SourceSize/dyadic/legacy material exports with `hSpectral := (spectral47_contract_iff _).mp (spectral47_exact_contract_inhabitant _)`, retaining every other guard. Then run an exact trace and a fresh review.
2. **Exact manuscript laws.** Natively prove the exact projected-energy equality, the s-factor eigenvalue (kernel-frame count), the G/Phi completion and marginal laws, and the invariant-first-argument adjoint. Alternatively, keep the manuscript text explicit that only the weaker inequality is formalized.
3. **Fidelity audit.** Compare against Lemma 4.7 and MZ24 A.13: attribution of the exact versus weaker bound, a notation crosswalk, and treatment of the unused guards and slack.
4. **Numeric NO.** Prove `hfail` at a useful e, bound B via Parseval, choose a, instantiate base and cutoff, give an effective L₀, and compare against the actual selection threshold.
5. **Joint witness.** Exhibit I with rows ≥ 1, padded copies, `TaggedGoodU`, A and `hsel`.
6. **Source and star.** Acceptance → fixed f, robust8S / `AllAmbientInverse`, the pre-draw global table, the physical sampler, κ and `hexpand`.
7. **R14.** Encoded or implicit reduction, a runtime proof, and learning.
8. **Upstream.** Post-audit, then the exact CMMSA transports.
9. **Custody and hygiene.**
   - Fresh-checkout replay with all hashes recomputed; reconcile the 687 count and the `BinaryMatrixFourier` identity.
   - Supply `GrassmannCounting` and `Diagonal` for review.
   - Clean stale banners, receipt flags and duplicate modules.
   - Dispose of the inherited warning and linter debt.
10. **Release.** Provider/citation/BibTeX/PDF QA and manuscript acceptance remain open. No overall GO is issued.
