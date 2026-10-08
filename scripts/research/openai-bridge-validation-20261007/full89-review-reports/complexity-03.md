# Partition 3/9 review: `ActualBinaryMatrixHC46A7T1Transfer.lean`

**Verdict: GO-WITH-NOTES.** This verdict covers only this file. It is not a verdict on the milestone, the A22/HC46 consumer chain or the campaign.

The file is mathematically sound as written. I found no blocking defects. Its meaning depends on definitions in other partitions, which are listed under integration questions at the end.

## What I could and couldn't check

- **Inspected:** `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7T1Transfer.lean`, in full. I read every declaration and proof body, from `T1IndexTriple` through `t1PointwiseFull_fourierIdentity`. I skipped no bodies.
- **Not checked:**
  - The SHA256 (`300CD79D…EF8A602`), because I had no way to hash the file.
  - The source index at `…\review-sources\source-index.json` and the 172-theorem list, because I had no tool access.
  - Whether the file compiles and its axiom profile. I'm relying on the reported GCP native results: seven zero exits and 172 standard axiom profiles.
- **Line numbers:** I didn't compute exact line numbers without tools, so findings point to declarations instead.
- **Forbidden constructs:** I searched the file text for `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `opaque` and `decide := true` overrides. None appear. The only global-style change is `attribute [local instance] Classical.propDecidable`, which is standard classical reasoning.

## Statements and their assumptions

| Declaration | Kind | Assumptions | Assessment |
|---|---|---|---|
| `t1TripleEquiv`, `t1TripleToMap_injective`, `t1TripleToMap_mapToTriple` | Unconditional | none | Correct. The triple (C, K, Xbar) matches the map A → W/B via kernel, range and the first isomorphism theorem. Both inverse laws are proved, not assumed. |
| `t1Triple_card` | Unconditional, gives the count | none | Count is 2^(dim A · dim(W/B)). This is right: Hom(A, W/B) over F₂ has dimension dim A · dim(W/B). It includes all zero-dimensional cases. No inequality or slack is involved. |
| `t1RankPrecedes_range_decomposition`, `t1RankPrecedes_agreement_on_preimage` | Conditional on rank additivity (`hXR`) | finite dimension | Correct: rank additivity forces range R = range X ⊕ range(R−X). |
| `t1Selected*` family (`_on_preimage`, `_ker`, `_range`, `_ambientH`, `_ambientC`, `_rankPrecedes`, `_hybridSelected`, `_active`) | Conditional on `hY : DR6OrdinarySelected A B Y` | uses `hY.1` (A ≤ range L) and `hY.2` (ker L ≤ B) | Correct. The selected triple gives H = B ⊔ Y⁻¹(A) and C = Yᵀ(B) ⊓ A. Rank additivity is proved from the direct sum (A/C) ⊕ (Yᵀ(B)/C), not assumed. |
| `t1ActiveTriple_forces_ordinary`, `t1ActiveTriple_unique` | Conditional only on activity | no `hY` | This is the reverse direction, and ordinary selection is derived rather than assumed. I re-derived it independently (details below). |
| `t1OrdinaryActiveEquiv`, `t1OrdinaryActive_sum_equiv` | Unconditional | none | A genuine bijection. `right_inv` relies on proof irrelevance for the Prop `DR6OrdinarySelected`. No selector injectivity is assumed. |
| `t1PointwiseFull_fourierIdentity` | Unconditional, the main result | no premises | Direction: the ordinary-filtered affine restriction (LHS) equals the sum over all triples of the typed W6 derivative (RHS). |

**Re-derivation of `t1ActiveTriple_forces_ordinary`:**
- **`hpre`:** We have q_C(a) ∈ range X ≤ range R, so some h ∈ H has L h − a ∈ C. Then C ≤ range L gives a w with L w = L h − a. The hybrid selector puts w in H, so h − w ∈ H and L(h − w) = a. This yields A ≤ range L.
- **`hOrdKer`:** If L w = 0, the selector puts w in H and R w = 0 lies in range X. Rank agreement gives X w = 0, and ker X = B ∩ H, so w ∈ B.
- **Theta agreement:** This follows from `t1TripleToMap_pullback_iff` together with `t1SelectedTheta_on_preimage`.

**How the main identity is proved:** The proof expands every per-triple derivative into a sum over all ambient Y (`t1TypedW6_collapse_parentFiber`), keeping every Y in each fiber, and swaps the two sums. For each Y it then shows:
- If Y is ordinary-selected, exactly one triple is active (`t1ActiveTriple_unique`). Its term equals the ambient term through the phase identity `t1OutputPhase`, which holds for any triple because of the physical square.
- If Y is not ordinary-selected, no triple is active.

The identity is not vacuous. For example, A = ⊥ and B = ⊤ is always ordinary-selected, and every `T1IndexTriple` type is inhabited by the zero map.

**HC46 unrestricted eta / A22 real-q:** This file has no eta or q parameter, and no hHC premise or other added hypothesis appears in any statement. So it neither restricts eta nor uses q. Whether the selected consumer actually uses these results with unrestricted eta and real q has to be checked in other partitions.

## Findings

None of these block the verdict.

1. **N1 (Low, integration).** In `t1PointwiseFull_fourierIdentity`, the local lemma `hactive_iff` proves `typedW6Precedes … ↔ t1ActiveTriple …` by unfolding definitions and closing with `rfl`. That only works if `typedW6Precedes` (defined in another file) is definitionally the same rank-additivity statement as `t1RankPrecedes`, with the same orientation: Z is the R map and X is the pullback. Compilation shows the two match. Whether that shared definition is the manuscript's predecessor relation still needs to be confirmed against the defining partition.
2. **N2 (Low, integration).** The main identity is only as meaningful as several definitions from other files:
   - `typedW6FourierDerivative`: its unfolding must be exactly ∑_Z [precedes]·coeff·χ_Z(Mraw), with no normalization factor.
   - `filteredCarrierFunction`, `complexAmbientAffineRestrict`, `complexAmbientHybridFilter` and `DR6ComplexOrdinaryFilter`.
   - `dr6_complexSelector_iff_actualOrdinary`.
   - The A18 lemmas `complexCarrierFourierCoeff_finset_sum`, `_smul` and `_character`.

   Normalization constants and the character sign convention live in those files.
3. **N3 (Low).** `t1TypedW6_eq_actual` simply restates `typedW6FourierDerivative_eq_actual` with offset argument `0` passed to `actualW6Derivative`. Nothing in this file uses it. Its downstream consumer needs to confirm that offset 0 is the intended specialization.
4. **N4 (Info).** `set_option maxHeartbeats 2000000` on `t1Triple_card` affects performance only, not soundness. Inside the proof, `letI` re-declares a `Fintype` instance that has the same definition as the global `t1TripleFintype` instance. This is fine because the file compiles, though the proof is fragile if Mathlib changes.
5. **N5 (Info).** The `FiniteDimensional F U` hypothesis on the two `t1RankPrecedes_*` lemmas is never used. It's harmless, but it slightly narrows the statements.
6. **N6 (Info).** `t1OrdinaryActiveEquiv.invFun` uses `Classical.choose` and is noncomputable. That suits counting and reindexing sums, but the equivalence has no computational content.
7. **N7 (Info, accuracy).** The module header says the quotient isomorphism, its pullback X̃ and the original map R = q_C Y|_H are kept distinct, and the code is consistent with that. `t1SelectedRestriction_eq_pullback_add_B` shows R = X̃ + q_C(Yᵀb) without identifying the two, and no lemma assumes the frequency-restriction map is injective.

## Questions left open for integration

- **Definitions from other files:** the precise definitions of `DR6OrdinarySelected`, `BinaryMatrixNestedSelectorA1.Selected`, `typedW6Precedes` and `typedW6FourierDerivative`, and of `BinaryMatrixA1Phase.traceCharacter_carrier_base_general`.
- **The consumer:** how the selected A22/HC46 consumer uses `t1PointwiseFull_fourierIdentity` and `t1Triple_card`, including any later exponent bound built from 2^(dim A · dim(W/B)).
- **External libraries:** the Mathlib lemmas this file relies on (`quotKerEquivRange`, `finrank_linearMap`, `card_eq_pow_finrank`, `quotientQuotientEquivQuotientAux_mk_mk`, `FunLike.fintype`) are trusted pinned library code, not newly reviewed here.
- **Out of scope:** everything named as open in the brief, including Spectral47, source/star/robust8S/numericNO, the encoded reduction, runtime/learning, upstream bridges and the manuscript/render/novelty gates. Nothing here supports any acceptance claim for them.
