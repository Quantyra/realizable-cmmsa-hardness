# Actual source-star soundness non-claims-boundary review

**GO-WITH-NOTES.**

Frozen source `f35269d0abecc290f2d79e25a2b1a470d738dc43`. Gate logs name `f35269d`, not `bba6dbb`. Main `ActualSourceStarSoundness.lean` SHA-256 `0C42DE927035271B413CB57F25C631BE076E7140BB365125AB06208A47BF6F9B`. Checks SHA-256 `2870AAA586F4DF0C873983906B6D30A269CED6B2ED3CFABC42F5330CF7BA254D`. Evidence `research/evidence/2026-09-16-actual-source-star-soundness-fresh-run/`. Independently rehashed local sources match the freeze and the gate. Certification commit `ce9ac48` did not change the Lean sources.

Accepted, NO/soundness of packaging only:

- `questionFailIndicator` is the `0/1` existential of `badRow` on `P.U`.
- `questionFailIndicator_eq_zero_iff` / `eq_one_iff`: that indicator is `0` iff `RespectsAt P rfl (honestRawLabel x)`, and `1` iff the honest pairing does not respect.
- `presentedEnum` enumerates `P.U` in `Fin J` along `P.card_U`; `mem`/`surj` make the `Fin J` exists match `actualBaseFailureIndicator I x (presentedEnum P)`.
- `questionFail_sourceExtension_original`: on original-row presentations (`hU : ∀ e ∈ P.U, ∃ r, e = Sum.inl r`), the indicator of `I.sourceExtension y` is the original-row `sourceBadRow` exists.
- `anyQuestionFailIndicator_le_sum`: union bound over a `Fin n` family of presented leaves.

Theorems live in namespace `ActualPresentedLeafGluing`. The only source doc comment is the indicator definition plus a next-consumer pointer. Checks invoke the exact exported signatures on a three-row mixed-RHS original-row fixture at `n = 1` and `n = 2`, plus empty `J = h = 0`. `#print axioms` is `propext`, `Classical.choice`, `Quot.sound` only. Main does not import `*Checks.lean`.

Notes, not blocking:

- Module/commit titles that say "source-star soundness" are catalog labels. They are not a decoder, NP-hardness, Theorem 1, Corollary 2, `SeededMap`, publication, or `P` versus `NP`.
- `RespectsAt P rfl` is honest packaging against the identity presentation, not silent identity-`Rel` star packaging and not `starAccepts` of a related family.
- The doc comment may cite certified `actualTaggedGoodFailureMean_sourceExtension_le` as a *consumer*. This module does not prove, re-prove, or export `(4/3)*J*eta`.
- `questionFailIndicator_le_sum` / `anyQuestionFailIndicator_le_sum` are `1`-versus-positive-summand bounds, not a mean bound.
- Checks may use original-row `J = 1`, `h = 0`, `K = ⊥`; the theorems keep their stated hypotheses (`hU` is required for the source-extension identification).

Forbidden claims absent. Manuscript theorem incomplete. Next: apply certified `actualTaggedGoodFailureMean_sourceExtension_le` to `presentedEnum`, then reduction assembly. Do not skip to Theorem 1.
