# Original block YES joint numerator

The Lean module `ActualOriginalBlockYesJoint.lean` proves the original-block term needed by the CMMSA manuscript's Equation (21) composition. It uses the committed exact raw ordered-question conditioning and declared post-padding `OriginalDraw` U-marginal bridge. This result does not establish the clique-resampled block terms or the full YES conclusion.

## Exact statement and quantifiers

Fix an actual occurrence instance `I`, a copied-row count `copies`, the question size `J`, and the center/leaf/arity parameters `t,h,k`. Assume nonempty raw ordered rows and `TaggedGoodU`, nonempty tagged center and conditional leaf fibres, and a positive number of tagged source rows. Fix one ambient linear assignment `f` before the draw. The explicit `PositiveErrorAssignment I copies f ε₁` premise is

`(badRows I copies f).card ≤ ε₁ * Fintype.card (TaggedRow I copies)`

over rational numbers, where a row is bad exactly when `f` evaluated on its source equation vector differs from its copied-source RHS. For any nonnegative `ε₁`, `original_block_joint_rejection_le` proves

`P_originalDraw[honestOriginalAssignment(f) rejects] * P_rawOrdered[legitimate] ≤ J * ε₁`.

The table `honestOriginalAssignment(f)` is fixed before the draw and is globally legal. `originalRejects_implies_badU` shows that rejection entails a bad equation among the sampled original U rows, regardless of center, leaves, or sampled class representatives. `raw_original_joint_le` proves `P_rawOrdered[legitimate ∩ containsBadRow] ≤ J ε₁` from the exact copied-row error premise. `conditioned_badU_joint_eq_raw` and `orderedToOriginalU_pushforward` identify that raw joint numerator with the bad-U marginal of the declared post-padding draw after multiplication by the raw legitimacy mass. Thus the final theorem bounds the actual original-block rejection event under the declared draw law.

No value of `τ` is fixed in this theorem. It applies after a later positive outer YES error `ε₁` has been chosen. `ActualLateTauPadding.exists_late_tau_padding` separately chooses copies after that later choice and proves the raw legitimacy mass is at least 3/4. The source-level existence of the copied-row assignment `f` satisfying `PositiveErrorAssignment` from the encoded positive-error YES instance is **not** proved here. In particular, the theorem does not claim that MZ's cited positive-error reduction already supplies the exact ambient linear-map representation used in this module.

## Verification and remaining composition

The targeted `lake env lean` check of the module completed successfully. `lake --old build PvNP.RealizableHardness.ActualOriginalBlockYesJointChecks` completed successfully (3443 jobs) after a normal parallel Lake attempt exhausted local memory in imported dependencies. The Checks file prints the statements and axiom dependencies of the eight main theorems; each reports only `propext`, `Classical.choice`, and `Quot.sound`. The source-check boundary is the direct finite copied-source row equation used in `BadRow` and the previously proved `ActualHonestTaggedTransport.honestOriginalAccepts_of_goodU` implication. A kernel axiom audit alone does not establish the external encoded reduction or its assignment representation.

The first missing YES theorem is the corresponding joint numerator bound for each actual clique-resampled block on one joint `m+1` draw law, followed by transport of the all-good-block event to verifier acceptance. The cited outer positive-error assignment existence and polynomial-time encoded copy construction also remain external or open. The NO decoder and numeric NO-soundness gap are unchanged.
