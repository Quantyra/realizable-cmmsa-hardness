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

Public declarations added or retained in the draft are `fixedScore`, `fixedScore_bounds`, `fixedScore_eq_one_iff`, `restrictedPair`, `restrictedPair_window`, `restrictedPair_agreesOn_iff`, `restrictedZoomEquiv`, `restrictedAgreeingZoomEquiv`, `restrictedPair_agreement_eq_restricted_original_agreement`, `fixedScoreAgreementSupport`, `fixedScoreAgreementCarrierEquiv`, `fixedScoreRetainedAgreementCarrierEquiv`, `ambientW_apply_zoom_uniform`, `retainedW_apply_intersection_zoom_uniform`, `ambientW_fixedScore_mean_eq_agreement`, `retainedW_fixedScore_mean_eq_restricted_agreement`, `actualRowGrassEquiv`, `actualRowLeafEquiv`, `actualRowCoordinateTable`, `actualRowCoordinatePair`, `actualRowCoordinateAgreesOn_iff`, `actualRowZoomEquiv`, `actualRowAgreeingZoomEquiv`, and `actualRowAgreement_eq`. Sol's capture/check manifest must cover each declaration and the exact imported source pins.

The prior provider failures are preserved as reported observations only. A read-only search of the assigned S tree found no locally saved intermediate bytes or logs matching failure IDs `5b95fcc3-381a-44a1-a550-8ccb3e3ab414` and `211d4be0-73db-4a84-b86f-182b95f5f36f`, or the inactive `completion_exception_recovery` task. No lossless custody is claimed for those unavailable intermediates. The intact draft found at takeover was preserved before editing.

## Remaining work

Remaining to-do list: Sol must capture these exact source bytes, verify source and dependency pins/manifests and all public declarations, then compile and diagnose through the GCP-only loop. Finish the actual row-draw/retained-space and outer posterior integration, discharge `hdF` in the selected application, and run the required checks and reviews. No Lean/Lake execution, Git write, or acceptance is claimed in this offer.
