# Non-Claims Review: Partition 3/9

**Scope:** Full89 original A22/HC46/selected-consumer milestone, partition 3 of 9. This verdict covers only this partition. It is not a verdict on the whole campaign.

**Method:** I read the supplied file text only. I used no tools, ran no Lean/Lake, and did not open the source index. I did not recompute the SHA256 `300CD79D…EF8A602`, so the match between this text and the hashed file is assumed, not checked. I did not re-check the compile status, the 172-root membership or the axiom profiles; I take the GCP-native results as supplied.

## File inventory

| File | Status |
|---|---|
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7T1Transfer.lean` | **Inspected in full.** Every declaration body was read, from `T1IndexTriple` to the end of `t1PointwiseFull_fourierIdentity`. |

No supplied body was skipped.

## What the file establishes

The file proves exact equalities and equivalences. It contains no inequalities and no asymptotic or exponent bounds.

1. **Index triples match linear maps.** `t1TripleEquiv` gives `T1IndexTriple A B ≃ (A →ₗ (W/B))`.
   - Both inverse laws are proved.
   - Injectivity recovers C, then K, then `Xbar`.
   - `t1Triple_card` gives the count `2^(dim A · dim W/B)`, including zero-dimensional cases.
2. **Ordinary selection matches active triples.** `t1OrdinaryActiveEquiv` pairs ordinary-selected frequencies with active (frequency, triple) pairs. Both directions are proved:
   - **Forward:** `t1SelectedTriple_active` uses `hybridSelected` and `rankPrecedes`. Rank additivity comes from the image-sum fact (`range_eq_sup`) and the zero-intersection fact (`disjoint_displacement`).
   - **Reverse:** `t1ActiveTriple_forces_ordinary` derives `DR6OrdinarySelected` from activity alone, and `t1ActiveTriple_unique` then shows the triple is the canonical one.
3. **Main identity.** `t1PointwiseFull_fourierIdentity` holds for all `n d A B T f M`, with no hypotheses: the ordinary-filtered affine restriction equals the sum over all T1 triples of `typedW6FourierDerivative`.
   - Ambient frequencies that collide on the same restricted frequency are kept as separate summands (`t1FilteredCarrierFunction_fourierCoeff`, `t1TypedW6_collapse_parentFiber`).
   - Injectivity of restriction is never assumed.

## Checks

**Vacuity:** none found.
- Every conditional hypothesis (`hY`, `ht`, `hXR`) is discharged constructively inside the file.
- There are no positivity or nonemptiness premises, so the trivial cases n=0, d=0, A=⊥ and B=⊤ are included, not excluded.

**Quantifiers:** all theorems are universal over carriers, subspaces, Y, T, f and M.
- The "conditional" lemmas are stated as implications and are used only after their premises are proved.
- `t1ActiveTriple_unique` is conditional on activity. Its docstring calls it "unconditional", meaning it needs no extra premise beyond activity.

**Assumptions:**
- No `sorry`, `axiom`, `opaque`, `implemented_by` or `unsafe`.
- `autoImplicit false` is set.
- Classical reasoning is used: `Classical.propDecidable` as a local instance, and `Classical.choose` in `invFun`. This fits the stated standard-axiom profile.
- There is no hHC premise anywhere in the file.

**Semantics pinned definitionally inside this file:**
- `Selected C H L` unfolds by `change` (in `t1SelectedTriple_hybridSelected`) to `C ≤ range L ∧ ∀ w, L w ∈ C → w ∈ H`.
- `typedW6Precedes C H X Z` is definitionally `t1RankPrecedes X Z`; `hactive_iff` proves this by `rfl`.

**Proof direction:** the main identity rewrites the left-hand side, the ordinary projection, into the T1 triple sum. The direction matches the claim.

**Numerical exponent bounds:** none in this file. This is an algebraic transfer identity.

## Findings

| # | Location | Finding | Severity |
|---|---|---|---|
| F1 | Whole file | The file contains no η, no q, no A22 statement and no HC46 bound. The requested audits cannot be done from this partition: original HC46 with unrestricted η, A22 with real q, and the claim that no hHC premise is added. This partition only supplies an unconditional exact identity that a selected consumer could use. | Info (scope) |
| F2 | Docstrings of `t1SelectedTheta_ker` and `t1SelectedTriple_ambientC` | These say "Y(B) ∩ A", but the code uses `range(Yᵀ ∘ B.subtype)` with `Y.transpose.toLin' : W n → V d`. The code is internally consistent; only the prose uses a different convention. | Low (documentation) |
| F3 | `t1ActiveTriple_unique` docstring | It says "unconditional reverse uniqueness", but the theorem takes `ht : t1ActiveTriple …`. "Unconditional" here means no extra premise. | Low (wording) |
| F4 | `t1OutputEquiv_physicalSquare` docstring | It mentions an "affine embedding", but the stated square is linear (`T` is absent). The affine part only enters in `t1OutputPhase`. | Info |
| F5 | `t1Triple_card` | It needs `maxHeartbeats 2000000`. This is a performance setting with no soundness impact. Nothing in the main identity depends on this count. | Info |
| F6 | `hactive_iff` (`rfl`) and `t1OrdinaryActiveEquiv.right_inv` (`Subsingleton.elim`) | Both depend on how definitions in other files are written: `typedW6Precedes` must unfold to `t1RankPrecedes`, and `DR6OrdinarySelected` must be a `Prop`. A compile pass confirms both, but both would break if those definitions were refactored. | Info |

None of these findings is blocking, and I found no mathematical error in any proof body.

## Open questions for integration

These depend on other partitions or on external library boundaries:

1. **Definitions from other partitions must match the manuscript.**
   - `DR6OrdinarySelected` must mean `A ≤ range Yᵀ ∧ ker Yᵀ ≤ B`.
   - `DR6ComplexOrdinaryFilter`, `dr6_complexSelector_iff_actualOrdinary` and `complexAmbientAffineRestrict` need checking.
   - So do `filteredCarrierFunction`, `complexAmbientHybridFilter` and `typedW6FourierDerivative`, plus `typedW6FourierDerivative_eq_actual` and its carrier equivalences.
2. **Phase and Fourier lemmas** need checking: `traceCharacter_carrier_base_general`, `traceCharacter_eq_matrix_character`, the `complexCarrierFourierCoeff_{finset_sum,smul,character}` lemmas, and `nestedDomainEquiv`.
3. **Consumer path.** Integration must confirm which of the 172 roots consume `t1PointwiseFull_fourierIdentity` or `t1OrdinaryActiveEquiv`. It must also confirm that the HC46 (unrestricted η) and A22 (real q) consumers use it with no added hHC premise.
4. **Library boundary.** The proofs rely on the trusted pinned Mathlib names `Submodule.quotientQuotientEquivQuotientAux_mk_mk`, `FunLike.fintype` and `Module.finrank_linearMap`. These are not newly reviewed here.
5. **Source hash.** The SHA256 match between this text and the indexed file has not been checked.

## Verdict: **GO-WITH-NOTES**

This verdict covers partition 3/9 only, a single file that I inspected in full. Its exact T1 transfer identity and the ordinary-to-active bijection are unconditional, non-vacuous and proved in the stated direction. The notes are documentation and dependency items only.

This is not a verdict on HC46 or A22 themselves: η, q and hHC usage are out of this file's reach (F1, open question 3). Everything listed as open in the brief remains open, including the broader Spectral47 work, the upstream bridges and the manuscript, render and novelty gates.
