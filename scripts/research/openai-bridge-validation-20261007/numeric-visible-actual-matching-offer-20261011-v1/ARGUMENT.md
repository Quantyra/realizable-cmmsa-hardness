# Actual visible matching bound after restriction

E002/S3137. Candidate argument only; uncompiled and unaccepted. This successor preserves every captured predecessor and uses a disjoint dependency rebind to functional-assignment v2.

## Pointwise bound for the actual retained/visible strategy

Fix the original coordinate ambient E, an actual retained subspace V, an original advice Q, and a decoded pair P=(W,g) with codim_E(W)≤r and Q≤V. The actual restricted decoder is P'=(W∩V,g|_{W∩V}), represented by `restrictedPair`. Its window is contained in V by construction. The actual restricted-visible agreement theorem is applied only to P': its support premise is `(W∩V)≤V`, and it supplies the dyadic-loss lower bound between the original H table and the visible table in original coordinates, both evaluated on P'. We then transport that exact restricted-pair agreement to the globally defined visible-coordinate table by the captured `actual_visible_agreement_eq_retained` identity, using Q≤V. The original unrestricted P is never passed to the loss theorem with a false support premise.

Push P' through the retained-to-visible linear equivalence e:V≃B, where B is `visibleCoordinateSpace X`. This gives the actual visible pair P0. Its visible codimension is

`codim_B(P0.W) = dim(V) - dim(W∩V) = dim(W+V) - dim(W) ≤ dim(E) - dim(W) = codim_E(W) ≤ r`.

The middle equality is the finite-dimensional sum/intersection formula; the inequality follows from W+V≤E. No equality/rank-stability premise is used.

Now fix any visible functional f compatible with P0. Its pullback f∘e agrees with g on W∩V. The set of full extensions F of g on E whose restriction to V equals f∘e is exactly the set of extensions of the uniquely glued functional on W+V. Therefore the event has cardinality `2^(dim(E)-dim(W+V))`, while the whole extension fiber of g has cardinality `2^(dim(E)-dim(W))`. Under the uniform full-extension law its probability is

`2^(-(dim(W+V)-dim(W))) = 2^(-codim_B(P0.W)) ≥ 2^(-r)`.

This is the general exact restriction-fiber count; it does not assume W+V=E. Expanding the finite pushforward law and summing this conditional bound over the compatible visible outputs gives the usual product-law matching lower bound. The total visible-list strategy supplies compatible mass at least `1/((r+1)*card(list_j))` for the actual cardinal of the list at the selected level. Hence the final exact-card statement is `1/((r+1)*card(list_j)*2^r) ≤ matching probability`. The list-card bound imported from Theorem 5.26 remains a separate theorem application and is not assumed here.

The visible functional comes only from X and the global visible table. Its restriction to V agrees with the original retained functional exactly when their induced assignments agree on every retained variable, by the captured functional-assignment-v2 theorem. Separately, when the full decoder's original H restriction equals the canonical RHS functional, every full extension satisfies every actual tagged equation under its induced original assignment. This RHS hypothesis is to be obtained from the actual favorable full-decoder witness; it is not replaced by a supplied equation-validity premise.

## Scope and unresolved work

This successor is limited to the actual pointwise matching and assignment bridge. It does not prove a row-draw probability estimate, a posterior mass bound, the all-maximal-pair list count, a global source-game law, the imported MZ24 count, the source NO conclusion, or GCP/runtime/certification acceptance. The generalized restriction-fiber count is a local proof obligation in the Lean source and remains unverified until Sol's compiler run. The captured geometry source and its manifest remain byte-for-byte unchanged; the new environment must resolve its `ActualFunctionalAssignmentAcceptance` import to the exact v2 source/capture identity, while preserving the historical v1 pin in the old geometry capture.

Remaining to-do list: translate the exact arbitrary-W,V restriction-fiber count and actual strategy application; include all exact source/manifest pins and axiom checks; obtain exact capture ACK; compiler acceptance and all downstream global/count/runtime gates remain open.