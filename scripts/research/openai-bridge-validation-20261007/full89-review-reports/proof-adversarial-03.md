# Partition 3/9 review: `ActualBinaryMatrixHC46A7T1Transfer.lean` (proof-adversarial)

**Verdict: GO-WITH-NOTES.** This covers only this one file. It is not a verdict on the whole campaign.

I had no tools, wrote nothing and used no subagents. I reviewed only the pasted file text. I did not open the source index, and I could not recompute the SHA256 (`300CD79D…A602`), so the hash is taken as given.

## Coverage

| File | Status |
|---|---|
| `lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A7T1Transfer.lean` | **Inspected in full**: every declaration body, from `T1IndexTriple` through `t1PointwiseFull_fourierIdentity` |

No body was skipped. The packet has no line numbers, so findings below are tied to declaration names rather than invented line numbers.

## Trust and vacuity

- **No forbidden trust escapes.** The file has no `sorry`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque` or `@[extern]`. Its only local trust settings are `Classical.propDecidable` (local instance) and the `classical` tactic. Both are consistent with the claimed standard axiom profile.
- **No hHC, η or q premise anywhere.** The only hypotheses are structural: `hY : DR6OrdinarySelected`, `hXR : t1RankPrecedes`, `hBH : B ≤ H`, and activity `ht`.
- **The headline theorems are unconditional.** `t1Triple_card`, `t1TripleEquiv`, `t1OrdinaryActiveEquiv` and `t1PointwiseFull_fourierIdentity` hold for all `A`, `B`, `T`, `f`, `M`, with no extra hypotheses.
- **No hypothesis is vacuous.** Each one can be satisfied, and the file itself proves this: `t1SelectedTriple_active` produces an active triple from any ordinary-selected `Y`. `DR6OrdinarySelected` itself can be satisfied, for example with `A = ⊥, B = ⊤`, or with any `Y` satisfying `A ≤ range Yᵀ` and `ker Yᵀ ≤ B`.

## Direction, quantifiers and numbers

- **`t1Triple_card`:** the count is `2^(dim A · dim(W/B))`, via `Module.finrank_linearMap` (the dimension of Hom(A, W/B)). The exponent and the order of the factors are correct, and the zero-dimensional cases are included. This is the only numerical exponent statement in the file.
- **Both directions of the ordinary/active correspondence are proved:**
  - Ordinary implies active: `t1SelectedTriple_active`.
  - Active implies ordinary, with the encoded map equal to the selected θ: `t1ActiveTriple_forces_ordinary`.
  - Together these give `t1ActiveTriple_unique` and the equivalence `t1OrdinaryActiveEquiv`. `right_inv` relies on `DR6OrdinarySelected` being a `Prop`, which holds because it is used in an `if`.
- **The rank-additivity predicate matches the one in the transported file.** `hactive_iff` closes by `rfl` after unfolding `typedW6Precedes` and `t1RankPrecedes`. So the kernel has checked that the two are the same definition, not just the same in name.
- **Frequency collisions are kept explicitly.**
  - `t1FilteredCarrierFunction_fourierCoeff` keeps every ambient `Y` in each fibre.
  - `t1TypedW6_collapse_parentFiber` uses `Finset.sum_eq_single` only in the parent-frequency variable `Z`, never in `Y`.
  - The docstring's claim that injectivity is not assumed is accurate.
- **The main identity is an equality, so there is no direction issue.** For each `Y`, either:
  - the ordinary case contributes exactly the canonical triple, with the phase matched through `t1OutputPhase` and `t1CarrierPhase_general`; or
  - the non-ordinary case contributes zero, because no triple is active.

## Findings

| # | Declaration | Severity | Finding |
|---|---|---|---|
| F1 | `t1PointwiseFull_fourierIdentity` (whole file) | Note / integration | The file contains no HC46 η, A22 q or selected-consumer statement. It is an exact algebraic transfer identity. Whether the original unrestricted-η HC46 and real-q A22 consumers use it without an added hHC premise cannot be decided from this partition. |
| F2 | `t1PointwiseFull_fourierIdentity` | Note | The right-hand side sums over all `2^(dim A·dim W/B)` triples. Only one term per `Y` is non-zero, but any downstream triangle-inequality or Cauchy–Schwarz bound over `t` picks up this count. Downstream exponent bookkeeping should be checked against `t1Triple_card`. |
| F3 | `t1ActiveTriple_unique` docstring | Info | It says "unconditional", but the theorem is conditional on activity `ht`. The intended meaning is "no injectivity premise". The statement is correct; only the wording could mislead. |
| F4 | `t1OrdinaryActive_sum_equiv` | Info | This is a generic reindexing along an equivalence. It is correct but has no mathematical content beyond `t1OrdinaryActiveEquiv`. |
| F5 | `hterm` inside the main theorem | Info | The phase equality is proved without using `ht`, so it holds for every triple. This is harmless; it just means the activity guard comes only from the `if` condition. |
| F6 | File-level `Classical.propDecidable` | Low | The `if`s in the statements use classical decidability. Consumers that state related sums with a different `Decidable` instance need `if_congr` or `simp` alignment. This is a usability risk, not a soundness one. |
| F7 | `t1Triple_card` | Info | `maxHeartbeats 2000000` is a performance setting only. |

## Open items for integration (unresolved here)

1. The definitions of the following live in other partitions and must be checked there:
   - `DR6OrdinarySelected`: assumed here to be `A ≤ range Yᵀ ∧ ker Yᵀ ≤ B`, as the uses of `.1` and `.2` imply.
   - `DR6ComplexOrdinaryFilter`, `dr6_complexSelector_iff_actualOrdinary`, `complexAmbientAffineRestrict`, `filteredCarrierFunction`, `typedW6FourierDerivative`.
   - `complexFourierCoeff`, including its normalisation.
   - `traceCharacter_carrier_base_general`, `traceCharacter_eq_matrix_character`, `complexCarrierFourierCoeff_{finset_sum,smul,character}`, `nestedDomainEquiv`, `typedW6FourierDerivative_eq_actual`, including the meaning of its `0` argument.
2. Which of this file's declarations are among the 172 roots, and whether the A22/HC46 consumer actually calls `t1PointwiseFull_fourierIdentity` or `t1Triple_card` (I did not read the source index).
3. The Mathlib lemma names this file relies on (`Module.card_eq_pow_finrank`, `Module.finrank_linearMap`, `quotientQuotientEquivQuotientAux_mk_mk`, `map_equivMapOfInjective_symm_apply`) fall under the pinned-library trust boundary. They are trusted, not newly reviewed here.
4. All the other open gates stay open: broader Spectral47, source/star/robust8S/numericNO/encoded reduction/runtime/learning, upstream bridges, and manuscript/render/novelty.
