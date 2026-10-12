# Actual fixed-score and conditional-agreement argument

Status: substantive author translation is present in `ActualFixedScoreConditionalAgreement.lean`. The source has not been compiled, so these declarations are an unverified draft, not a verified result or certification. No theorem assumes the desired conditional-agreement identity or posterior success mass.

## Fixed score and ambient identity

For fixed actual table `T`, advice `Q`, and original decoded pair `P`, `fixedScore T Q P L` is defined before the deletion draw. It is one precisely when `L ≤ P.W` and the original table agrees with `P.g` restricted to `L`; otherwise it is zero. `fixedScore_bounds` and `fixedScore_eq_one_iff` state its elementary range and exact event.

Under `Q.val ≤ P.W`, `a ≤ d`, `d ≤ finrank P.W`, and `d ≤ J`, `ambientW_apply_zoom_uniform` proves the exact conditioned density on `Q ≤ L ≤ P.W`. The finite sum in `ambientW_fixedScore_mean_eq_agreement` reduces that density to the size of the fixed-score support divided by `gaussian (finrank P.W-a) (d-a)`. `fixedScoreAgreementCarrierEquiv` identifies this support with `AgreeingZoom`; `card_relativeUpper` gives the zoom denominator; `agreement_eq_fraction_of_nonempty` then proves the mean is exactly `agreement T Q P`.

## Retained identity and restricted pair

For a draw `s` containing `Q`, the same score is conditioned on the intersection of `P.W` and `retained s`. `retainedW_apply_intersection_zoom_uniform` gives exact uniform mass there under the explicit positive-fiber guard `hdF : d ≤ finrank (P.W ⊓ retained s)`. The `hdF` guard is essential and remains explicit. The selected application must discharge it using the actual restricted-pair lower-rank result and selected-window slack.

`restrictedPair` retains the original `Q`, intersects only the original window, and restricts the original functional through the inclusion. `restrictedPair_agreesOn_iff`, `restrictedZoomEquiv`, and `restrictedAgreeingZoomEquiv` identify the restricted zoom and agreeing zoom with the corresponding original carriers inside `retained s`. `retainedW_fixedScore_mean_eq_restricted_agreement` proves the fixed-score mean equals the canonical agreement of that actual restricted pair. `restrictedPair_agreement_eq_restricted_original_agreement` treats zero-card zooms separately and uses the inclusion of agreeing leaves into the zoom carrier to show the numerator is also zero. The proof preserves the pointwise score and does not replace the requested identity by a hypothesis.

If `Q` is not contained in the retained space, the draw-specific posterior atom is zero. This draft makes no arbitrary decoder assignment on that zero-weight atom and does not yet formalize the outer posterior sum.

## Actual row-coordinate transport

For each fixed actual good object `U`, `actualRowGrassEquiv` is induced by exactly `ActualTaggedRowDeletion.actualRowCoordinateEquiv I copies U`. `actualRowCoordinateTable` transports every leaf label through the induced leaf-domain equivalence. `actualRowCoordinatePair` transports the whole decoded window and functional through the same frame. `actualRowCoordinateAgreesOn_iff` proves the pointwise table/pair identity; `actualRowZoomEquiv` and `actualRowAgreeingZoomEquiv` transport both carriers; `actualRowAgreement_eq` proves exact rational agreement equality.

The pointwise transport is stated with `AgreesOn`'s actual signature: the table is explicit, while the transported pair is supplied through its implicit `P` parameter. The row deletion source also provides `actualRetained_map_coordinates`, `rowDrawEquiv`, and `actualRowDrawMass_eq`. Their integration with the identities above and the actual joint posterior law remains open; no independent frame or surrogate draw law is used here.

## Pinned inputs and custody boundary

The source imports `ZoomOutTransfer`, `ActualFiniteLaw`, and the candidate `ActualTaggedRowDeletion`. The intended Full107 source record is `full107-trace-qualified-source-record-v1/review-sources/lean/PvNP/RealizableHardness`; the Full114 row-deletion offer is `numeric-row-deletion-offer-20261011-v1/ActualTaggedRowDeletion.lean`, SHA-256 `F844D422FEF025399462872F9F59D6EC1E8BA41C28DCE4D95B20C463B876390B`. The Full114 input archive SHA-256 is `70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04`; this offer does not assert that archive was accepted.

Public declarations covered by `Checks.lean` are every `def` and `theorem` in the source; every theorem also has a `#print axioms` request. This includes the generalized fixed-score/restriction carriers, both finite-law mean identities, the actual row-coordinate frame and dependent carrier transports, codimension and retained-intersection identities, generic disjointness-event transport, pointwise score comparison, and the actual-frame ambient mean identity. The V3 manifest enumerates the same declarations and pins the exact source, checks, argument, imports, and dependency set.

The prior provider failures are preserved as reported observations only. A read-only search of the assigned S tree found no locally saved intermediate bytes or logs matching failure IDs `5b95fcc3-381a-44a1-a550-8ccb3e3ab414` and `211d4be0-73db-4a84-b86f-182b95f5f36f`, or the inactive `completion_exception_recovery` task. No lossless custody is claimed for those unavailable intermediates. The intact draft found at takeover was preserved before editing.

## Remaining work

Remaining to-do list: Sol must capture these exact source bytes, verify source and dependency pins/manifests and all public declarations, then compile and diagnose through the GCP-only loop. Finish the actual row-draw/retained-space and outer posterior integration, discharge `hdF` in the selected application, and run the required checks and reviews. No Lean/Lake execution, Git write, or acceptance is claimed in this offer.
## V3 row-frame and posterior identities

V3 retains the V2 fixed-score and conditional-mean arguments, and adds a pointwise score comparison: where the actual full table equals a visible table on a leaf, the original pre-draw score is at most the visible-table score for the same original pair. This is a local implication for use with an explicitly proved exceptional-event bound; it does not assume table agreement or import a posterior success-mass hypothesis.

For the fixed actual row frame, `actualRowCoordinatePair_codim_eq` preserves ambient codimension. `actualRowRetainedIntersection_map_eq` and `actualRowRestrictedPair_window_eq` identify the mapped actual intersection with the coordinate retained-space intersection. The whole restricted pair remains transported through `actualRowCoordinatePair`, including its functional, and `actualRowRestrictedAgreement_eq` identifies the exact canonical agreement in that frame. `actualRowFixedScore_eq` gives pointwise score equality under the same frame. `actualRowDisjoint_iff_map` gives the exact disjointness-event equivalence for any two subspaces already represented in the actual coordinate space; applying it to concrete original and completion equation subspaces still requires presenting those spaces in that coordinate carrier and proving the completion-selector links.

The dependent inverse carrier cast in `actualRowAgreeingZoomEquiv` is explicit through `e.apply_symm_apply` before applying the agreement iff. The restriction-before-frame and frame-before-retained-window identities are stated at the actual window level, while the transported dependent pair carries the restricted functional.

This source remains an uncompiled author draft. It does not import the historical completion-pullback candidate, invoke native Lean/Lake, or claim an accepted result. The actual completion-event integration, instantiation of the posterior visible-table equality away from the captured exclusions, and the outer joint-law application remain required. The two frozen posterior components remain dependencies by mathematical identity only; this file proves no posterior mass premise in their place.

Remaining to-do list: connect concrete original/completion equation spaces to the actual coordinate carrier, instantiate the table-equality side condition from the selected fixed row frame and captured exclusions, compose the fixed-score identity with the actual generic joint-score-loss lemmas, then obtain GCP compilation and required review. Finish the wider decoder/source-NO and runtime/certification obligations.
## V4 restriction-frame mean identity

V4 proves equality of the whole transported restricted pair with the restriction of the transported original pair. The dependent functional is compared after the window equality, using the actual submodule equivalence maps; the proof does not infer equality from window dimensions or window equality alone. It then composes the retained conditional mean theorem with this pair equality and the actual row-frame agreement theorem, obtaining the retained fixed-score mean as the canonical agreement of the actual restricted pair. The coordinate positive-fiber guards remain explicit in the theorem signature. No actual selector/transversality or posterior event is assumed by this identity.

The V4 source and Checks remain uncompiled. The source has not been offered for immutable capture pending static review of the dependent functional transport. V3 remains separately captured and unchanged.