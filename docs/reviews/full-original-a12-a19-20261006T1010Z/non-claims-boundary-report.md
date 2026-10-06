# Non-claims-boundary review: original A12 and A19 (capture59)

This is a separate top-level review covering only the non-claims-boundary lens. It uses only the supplied packet. I made no tool calls and ran nothing. Compile and axiom facts come from the supplied gate JSON and raw output. No verdict from another lens is combined here.

## 1. What the frozen bytes actually prove

The owner source is `ActualBinaryMatrixHC46A12InfluenceBound.lean`, SHA-256 `9AAFDAD1…5BAED`. Its checks file is `47A86423…DFA`.

**`manuscript_A12_actual` (lines ~283–298)**
- Holds for all `n d D`, every `eta : Real` and every `f : BinaryMatrix n d → Complex`.
- Hypotheses are only `ComplexFourierSupportedThrough D f` and `OriginalActualInfluenceThrough D eta f`.
- Conclusion: `uniformMean(|f|²)²` is at most `2^(103·D²)·eta·uniformMean|f|²`, i.e. E|f|⁴ ≤ 2^{103D²}·η·E|f|².
- This matches paper/body.tex (A12): "‖f‖₄⁴ ≤ 2^{103d²}η‖f‖₂²" under "all influences … through order d at most η".
- There is no Q premise, no positivity on D, no bound η ≤ 1, no ambient-width condition and no complement argument.
- η ≥ 0 is derived inside the proof (`a12_influence_parameter_nonneg`, from the ⊥/⊤ order-zero instance). D = 0, η = 0 and zero-width spaces are covered by the quantifiers.

**`manuscript_A19_actual` (lines ~300–315)**
- Hypotheses are only rank support ≤ D and `UpToActualNormSqGlobal D eps f`.
- Conclusion: E|f|⁴ ≤ 2^{114D²}·ε·E|f|².
- This matches (A19).
- The influence premise is built by `filteredCarrierFunction_energy_le_A16` for **every** (A, B, T). The cost bound `_hcost` is never used, so A16 is consumed in a form stronger than the manuscript's "k ≤ d".
- The exponent arithmetic is 103 + 11 = 114 via `pow_add`/`ring`.

**The definitions behind the final statements are all in the packet.** The meaning of both statements rests on these definitions, and every one of them is supplied in full:
- `uniformMean`, `character`, `pairing`
- `complexFourierCoeff`, `ComplexFourierSupportedThrough`
- `OriginalActualInfluenceThrough`, `carrierMean`
- `filteredCarrierFunction`, `complexAmbientHybridFilter`, `complexAmbientAffineRestrict`, `Selected`
- `UpToActualNormSqGlobal`, `ActualAffineRestriction.order`/`.fibre`, `fibreEnergy`

The influence definition takes the full normalized mean over each carrier `Hom(V/A, B)` at base `T + j_B M q_A`. The globalness definition covers every actual affine restriction of order ≤ r at every base, including order zero. Both match the manuscript wording.

**What this means for the boundary.** Proofs that were not reviewed here (the A7 graph and the omitted sources) cannot change what the two statements mean. They can only matter through kernel soundness and the axiom profile. All 68 profiles are {propext, Classical.choice, Quot.sound}. That covers `manuscript_A12_actual`, `manuscript_A19_actual` and `filteredCarrierFunction_energy_le_A16`.

## 2. Findings on the proposed wording

**N1 (Medium, wording). "Certified" is the wrong word.**
- The proposal reads: "original A12/A19 certified with notes".
- The accepted A7 lineage used "ACCEPTED WITH NOTES" and kept `full_manuscript_certified: false`.
- "Certified" invites reading this as manuscript certification.
- Recommendation: "accepted with notes at formal-statement level for `manuscript_A12_actual` and `manuscript_A19_actual` at source 9AAFDAD1 / Checks 47A8 / capture59 manifest 91E390F5 / run `cmmsa_a8_output_20261006T095324Z_3ea31944`."

**N2 (Medium, trust-boundary accuracy). Some omitted or unsupplied sources are on the critical path.**
- `ActualTypedABCanonicalFlag` uses `ActualMZ24HyperplaneSupport.exists_hyperplane_containing_of_ne_top`, `relativeCodim` and `relativeCodim_eq_finrank_sub`. That file is one of the **64 omitted** sources.
  - The call chain is `fullCodomainHyperplaneFlag` and `codomainFlagToSubcarrier` → `exists_canonical_source_flags` → `filteredCarrierFunction_energy_le_A16`.
  - So the preparation index's description of the omitted set ("primarily outer/star/MZ/covering branches reached through umbrella imports") does not hold for this file.
  - Soundness impact is nil: the result is used only to choose a flag existentially, it is kernel-checked under standard axioms, and the fact itself is elementary (a proper subspace lies in a hyperplane).
  - The record should still name it as a trusted, unreviewed critical-path dependency.
- The A12 Parseval step (`A12FourthMoment`, file supplied) relies on lemmas whose sources are not supplied:
  - `filteredCarrierFunction_fourier_expansion`, `complexFourierCoeff_smul`, `complexFourierCoeff_character` and `complexFourierCoeff_finset_sum`. These come from `ActualBinaryMatrixHC46A18DerivativeRankProjection` or similar. That file is neither among the 94 supplied sources nor in the 64-omitted list.
  - `a12_selected_card_le` uses `a7_transpose_finrank`, and `a12_energy_mean_eq_mass` uses `a7MatrixLinEquiv` (both in A7Transfer, partially excerpted).
  - These are presumably covered by "accepted A7 proof graph", since A7Transfer itself calls `actual_affine_derivative_energy_eq_selected_fourier_mass`.
- Required: the final record should split all 217 sources into explicit buckets:
  1. the 94 supplied sources;
  2. the A7-lineage import closure reused by identity;
  3. the 64 omitted A16-umbrella sources.
- The two critical-path items above (and `A12FourthMoment`'s own frozen56 identity, if it is claimed under A7 lineage) should be listed by name. The record should not imply that bucket 3 is logically idle.

**N3 (Medium, missing non-claims). The proposal does not exclude A17, A18 or the post-A19 chain.**
- `actual_A18_original_global` (influence ⇒ globalness) sits in an imported file. It is not among the 68 profiles and was not reviewed. A12 and A19 consume only the *definition* `OriginalActualInfluenceThrough` from that file.
- Add, explicitly:
  - no acceptance of A13–A15 as standalone theorems, nor of A17 or A18;
  - no square-globalness, no all-dyadic-moment or Lp result after (A19);
  - no A20/A21/A22.
- The existing "no LP theorem / Spectral47 / HC46 inhabitant" exclusions are correct, but they do not cover these.

**N4 (Low–Medium). The scope of "A16 consumer path" is ambiguous.**
- State plainly that `filteredCarrierFunction_energy_le_A16` (source `A592FF69`, fresh standard profile) is accepted **only as consumed by A19 in this review**.
- That acceptance assumes `ActualMZ24HyperplaneSupport` (see N2) and the A7-lineage infrastructure.
- It is not standalone three-lens acceptance of the A13–A16 manuscript section. This matches the packet's own scope line.

**N5 (Low). The counting route differs from the manuscript's.**
- The formal count goes through flags injected into Submodule(R)², with |Submodule R| ≤ |End R| = 2^{r²} via surjective `range`. That gives ≤ 2^{2r²} ≤ 2^{3D²}.
- The manuscript's Gaussian-binomial expression and its intermediate bound (j+1)²·2^{j²} ≤ 2^{3j²} are **not** formalized.
- Acceptance wording should claim only the final factor 2^{3D²}. It should not claim that the manuscript's intermediate count is certified.

**N6 (Low). The A7 lineage now rests on comment successors.**
- `manuscript_A7_actual` is reused from source `B296A5A9`, a comment-only successor of the accepted `28C56AFA`. Run59 does provide the fresh exact-source native gate for it (owner identity B296A5A9 is in the gate map).
- The "all bytes outside nested block comments identical" check is supplied only as a summary, not as raw diff evidence.
- The wording should say A7 is reused through the accepted frozen56 review lineage plus that comment-identity claim. It should not say A7 was independently re-proved.

**N7 (Low). Stale disclaimers in supplied sources.**
- `GrassmannCounting.lean`, `GrassmannIncidence.lean` and `TripleRestrictionDimension.lean` carry headers saying "UNCOMPILED … No Lean4.34 verification or acceptance has run". `SubspaceRestriction` and `TripleRestrictionRank` say "independent review pending". All of these sit inside a closure that the gate reports compiled with no missing objects.
- The A11 and A7Transfer docstrings say A7 "does not establish … a Q upper bound". That remains true of A7 alone, but `a12_Q_le` now gives a **conditional** Q bound under the influence premise.
- None of this affects truth. The record should neither cite these headers nor resolve them by implication. Any refresh should be a later comment-only successor.
- Wording should say: "Q ≤ 2^{3D²}ηE|f|² holds only under the influence premise; there is no unconditional Q bound."

**N8 (Low, process and warnings). The proposal leaves out the warning and harness notes.**
- Add: the inherited 981 warning headers (and the cslib header where relevant) remain S3137 debt and are not discharged. The legacy generic RED audit and its 19-missing-profile parser diagnosis are preserved; the qualified full gate separately covers all 68 profiles.
- Add: the executed harness was pinned but not pushed at launch; it was pushed afterwards in `f1a5895d`.
- Add: the NEW59 assertion failure (expected 200 objects, actual 215) failed before cloud launch, and the receipt KeyError was repaired via the two authorized owned paths. Raw failures are retained, and neither repair changed any proof source.
- The gate's `"accepted": false` is correctly pre-review. The new record must not backdate acceptance onto the gate artifact.

## 3. What the proposed wording gets right

- It is limited to fourth-moment bounds.
- It excludes an HC46 inhabitant, an LP theorem, Spectral47, reductions, learning lower bounds, P-vs-NP, full manuscript certification, publication and release.
- It keeps S3132 PARTIAL and S3137 INCOMPLETE.
- It records helper credit as zero.
- It treats native green as necessary but not sufficient.
- The hypotheses of the statements match the requested "only support + influence" and "only support + globalness" restrictions, with η and ε left unrestricted.

## 4. Assumptions and trust limits

- Lean kernel soundness, plus the pinned Mathlib `Projection`, `exists_isCompl`, `finrank_linearMap` and `card_eq_pow_finrank` excerpts, used as library trust.
- The gate JSON, raw axiom output, custody hash and TERMINATED record are taken as supplied; I did not re-run or re-hash anything.
- Unreviewed but kernel-checked critical-path proofs: the A7 lineage (factor 100, degree-zero base, `a7_positive_of_mixed_bound`, `filteredCarrierFunction_supportedThrough`), the A18DerivativeRankProjection lemmas, and `ActualMZ24HyperplaneSupport`.

## 5. Verdict

The statements match the manuscript's A12 and A19 with no hidden premises. Adopt the wording with the amendments in N1–N4 (required) and N5–N8 (recommended): replace "certified" with "accepted with notes" and pin the exact bytes, name the critical-path trusted sources, add the A13–A18 and post-A19 exclusions, bound A16's acceptance to its use in A19, and add the warning-debt and harness-process statements.

GO-WITH-NOTES
