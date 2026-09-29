# Original ordered padding and U marginal

Scope: the CMMSA manuscript's late-padding YES denominator and original copied-row verifier first marginal. This is a force-bearing bridge for S3126/S3132, not a proof of the complete YES block estimate.

## Exact Lean result

`ActualOriginalOrderedPaddingLaw.lean` defines raw ordered copied rows as `Fin J → Fin copies × I.RowId`. Its legitimate event is the image of the committed `TaggedOrderedGood` type, and `legitimate_eq_actual_good` proves that this event is exactly `actualTaggedGoodQuestions`, not a second eligible predicate.

For every fixed actual occurrence instance `I`, copies, and `J`, with a nonempty raw ordered type, `raw_legitimate_mass_eq_actual_good` proves the raw uniform event mass equals `actualTaggedGoodMass I copies J`. With `0 < copies` and `0 < m`, `raw_legitimate_mass_eq_one_sub_bad` proves it is exactly `1 - actualTaggedBadMass I copies J`. The earlier `ActualLateTauPadding.exists_late_tau_padding` then supplies copies after the later positive tau choice, with bad mass at most both tau/100 and 1/4. No tau is selected when the present marginal theorems are stated.

For every eligible ordered tuple, `conditioned_ordered_point` proves its raw uniform mass divided by the legitimate mass equals its mass under `orderedGoodLaw`. For every tagged good row set U, `conditioned_taggedU_mass` sums this conditional point law over the exact orderings of U and obtains uniform `TaggedGoodU` mass. The proof uses the committed `orderedGood_pushforward` and its exact factorial fibre count.

For every fixed `I`, copies, `J`, `t`, `h`, and `k`, assuming a nonempty tagged good row type and nonempty conditional center and leaf fibres, `originalLaw_U_marginal` integrates the center, ordered leaf, and representative kernels of the declared `OriginalDraw` law and proves that its U projection is uniform `OriginalU`. `originalLawFromTagged_U_marginal` specializes this to the declared post-padding draw law. `conditional_raw_eq_originalDraw_U` proves equality, pointwise for every `OriginalU`, between the conditioned raw ordered-row U mass and that declared law's U marginal. The theorem does not identify all manuscript verifier fields or prove a verifier-level YES result.

These are exact finite-law identities. They do not require independence among the manuscript's resampled blocks, and they do not establish any of their per-block equation failure estimates.

## Verification and boundary

`lake build PvNP.RealizableHardness.ActualOriginalOrderedPaddingLawChecks` completed successfully (3437 jobs). The Checks file prints the statements and axiom dependencies of the eight principal theorems. Each reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. This axiom check verifies the local kernel dependency shape; it does not source-check every imported mathematical result or discharge the external CMMSA contracts.

| Review lens | Bounded U-marginal result | Equation (21) / core Theorem 1 |
| --- | --- | --- |
| Proof adversarial | GO-WITH-NOTES | NO-GO |
| Complexity theory | GO-WITH-NOTES | NO-GO |
| Non-claims boundary | GO-WITH-NOTES, with declared-law wording | NO-GO |

The remaining YES step is to prove, for each original and clique-resampled block, the actual joint failure event bound required by `ActualLateTauYesComposition.conditioned_yes_failure_le`. In particular the resampled question's U law is not certified by this original-U marginal. The actual representative-selection, changed-ambient 8S, MZ NO decoder, and encoded Theorem 1 composition remain open. This result does not change the numeric NO-soundness gap.
