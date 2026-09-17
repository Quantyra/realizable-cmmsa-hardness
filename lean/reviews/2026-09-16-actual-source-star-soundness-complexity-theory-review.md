# Source-star soundness complexity-theory review

**Verdict: GO-WITH-NOTES**

Frozen source `f35269d0abecc290f2d79e25a2b1a470d738dc43`. Independently rehashed main `0C42DE927035271B413CB57F25C631BE076E7140BB365125AB06208A47BF6F9B`, Checks `2870AAA586F4DF0C873983906B6D30A269CED6B2ED3CFABC42F5330CF7BA254D`; objects `AD8FFF6C…2527` / `1016B717…0CA2`. Evidence `research/evidence/2026-09-16-actual-source-star-soundness-fresh-run/` gate PASS naming `f35269d`. `#print axioms` standard only (`propext`, `Classical.choice`, `Quot.sound`). Forbidden-token scan clean.

## Force

`questionFailIndicator` is the 0/1 existential of `badRow` on presented `P.U`. Quantifiers are honest: the queried leaf, not the whole instance.

`questionFailIndicator_eq_zero_iff` / `_eq_one_iff` restate certified `honestRawLabel_respects_iff` as that indicator: the honest pairing `RespectsAt` iff every queried row has `badRow = false`. That is the leaf-side fact that a failing question cannot package the honest pairing. It is not a statement about other labels.

`presentedEnum` is `P.U.equivFin` transported along `P.card_U`. `presentedEnum_mem` and `presentedEnum_surj` make the image exactly `P.U`, so the exists over `Fin J` matches the exists over `U`. Injectivity is not stated; it follows from `U.card = J` plus surjectivity onto `U`, and is not needed for the existential.

`questionFailIndicator_eq_baseFailure` is the force-bearing carrier identification: the unordered leaf-fail event equals certified `actualBaseFailureIndicator I x (presentedEnum P)`. Same `Finite3LinSource.ofActual` `badRow`. This is the interface the next consumer needs to sit on the tagged-failure ordered-tuple carrier.

`questionFail_sourceExtension_original` is the required original-row specialization, not optional packaging. Hypothesis `hU : ∀ e ∈ P.U, ∃ r, e = Sum.inl r` is honest. The proof uses certified `ofActual_badRow` and `sourceExtension_original_bad`; `I.row (Sum.inl r)` is definitionally `I.originalRow r` and `rowRhs` is `rhs`. The identity is `sourceBadRow` on queried original indices, not cloud rows, not a global decoder.

## Packaging and theater

`questionFailIndicator_nonneg`, `_le_one`, `_le_sum`, and `anyQuestionFailIndicator_le_sum` are 0/1 splits and 1-versus-positive-summand bounds. `_le_sum` is over all `RowId`, not the `Fin J` union of `actualBaseFailureIndicator_le_sum`. Do not feed that all-row sum to a `(4/3)*J*eta` mean.

Module/route name "soundness" and freeze talk of "NO/soundness" overclaim the theorems. Nothing here mentions `starAccepts`, `LeafLabel` families, dishonest labels, or `leafFailIndicator`. Honest-pairing question-fail is the NO-side of honest completeness: if queried rows are violated, the honest pairing does not `RespectsAt`. It is not soundness against a cheating prover, and it is not "the star rejects." "The star cannot package an honest label on those questions" is only `¬ RespectsAt` of `honestRawLabel`.

`presentedEnum` is an enumeration, not a sampler. Certified `actualTaggedGoodFailureMean_sourceExtension_le` does not take `presentedEnum` as an argument; it averages `actualTaggedFailureIndicator` over uniform good tagged tuples. This module does not re-prove that mean and does not identify the law of a random presentation with that tagged carrier. Ordered sampling-with-replacement versus a `J`-set enumeration remains a next-consumer transport. Do not treat `eq_baseFailure` as already giving `(4/3)*J*eta` for a fixed `P`.

`anyQuestionFailIndicator` is an existential over an arbitrary `Fin n` family of presentations. It is not a multi-block resampling law, not clique stationarity, and not a probability union. No `PMF`, no expectation, no measure.

Not a decoder of a global assignment from agreeing labels. Completeness-review wording that the next consumer should bound `leafFailIndicator` of non-honest labels is not this increment; `leafFailIndicator` is untouched.

## Checks and non-credits

Checks invoke shipped theorems on the nonempty three-row mixed-RHS fixture: `honestAssignment` (unique nonzero-RHS original support bit) gives `questionFailIndicator = 0`; `violatingAssignment` (zeros) gives `1`; both run `eq_baseFailure` and `le_sum`. `anyQuestionFailIndicator_le_sum` at `n=1` and `n=2`; `n=2` uses distinct original rows 0 and 1. `questionFail_sourceExtension_original` is invoked on an original-row presentation, not evaluated to a concrete 0/1. Empty `J=h=0`: `U=∅`, `questionFailIndicator = 0` for every `x`. `#print axioms` standard. All nonempty fixtures are `J=1`, `K=⊥`, singleton original `U`; `J>1` enumeration is proved and not fixture-exercised.

Not NP-hardness. Not the `(4/3)*J*eta` mean. No `SeededMap`. Not credited: Theorem 1, Corollary 2, randomized reduction, P vs NP.

Usable as leaf-side honest-pairing question-fail, its identification with certified `actualBaseFailureIndicator` of `presentedEnum`, and original-row `sourceBadRow` specialization. Next consumer remains the tagged-failure mean as a *consumer* of that identification, plus the ordered/unordered law transport. Do not skip to Theorem 1.
