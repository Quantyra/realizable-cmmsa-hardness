# Full supplied-array prefix marginal

E002/S3137. UNCOMPILED and UNACCEPTED.

## 2026-10-11 The full supplied advice tuple and its used prefix

Fix the globally selected a<=r before any question. For each retained vector space V, split a full r-tuple of independently uniform vectors into its first a entries and remaining r-a entries. The finite function-space equivalence is a bijection, with total cardinal equal to the product of the two array cardinalities. Any score depending only on the first a entries is repeated exactly card(V)^(r-a) times in the full unweighted sum. Dividing by the full cardinal cancels that factor, so its expectation equals the existing uniform a-array expectation exactly. The empty prefix and empty suffix are covered, and V is nonempty because it is a vector space. This uses no independence conditioning and does not require the full r-tuple itself to be independent.

Apply this equality separately to every retained draw s, with the literal VectorAdvice output function on the first a vectors, zero score if that prefix is dependent, and the actual inclusion of its span into coordinate advice. Weight by the unchanged prior of s and sum. The resulting full-r-tuple score is exactly VectorAdvice.actualJointScore for the used prefix. Consequently the captured literal visible-event transfer applies with the same single error2^r/2^J; ignoring the unused vectors introduces no extra loss, rejection or resampling. Both provers can compute the same prefix because a is globally fixed. The visible/original coordinate transports, private output product and assignment acceptance still need their concrete application before this score is identified with the source game.

Remaining to-do list: translate and verify the full-array marginal identity and its literal visible-event application; complete the actual posterior/output/game-law joins, imported count, source NO and all native and certification gates.

This module translates the exact uniform prefix expectation and applies it to the literal visible joint event. It does not test unused vectors for independence, resample a failed used prefix, or add a second error charge. Actual coordinate/output and source-game acceptance identification remains open.
