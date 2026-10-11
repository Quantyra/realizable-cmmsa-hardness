# Restricting the original pair to the actual visible window

E002/S3137. Implements the window and label step of the already recorded 2026-10-11 Two-table leaf loss and the posterior margin argument. Uncompiled and unaccepted.

Given the actual original decoded pair P and a deletion draw containing Q, construct P' with window P.W intersect actualRetained and label P.g restricted by the actual inclusion. Its functional values are exactly the original values. The captured actual row-coordinate map equality and dimension-preserving linear equivalence identify actualRetained dimension with 3J minus twice the original draw's drop count.

The finite subspace dimension-addition formula and dim(W+V)<=dim(E) imply dim(W intersect V)>=dim(V)-codim(W). Thus original codimension at most r and drop count at most T imply dim(P'.W)>=3J-2T-r. No rank-stability premise is needed for this lower bound; rank stability remains necessary for the later random-extension calculation.

Under the explicit scalar slack J+2h+1<=3J-2T-r and advice/query guards, all interval-transversality guards hold for P'. The captured actual visible-table comparison then applies, and monotonicity of the reciprocal power bounds its error by 2/2^(2J-2T-2h-r-1). Both original and completion advice-transversality premises are retained, and their exclusions must still be charged under the posterior. No existence of a favorable draw or changed draw law is asserted. The complete posterior integration and selected numeric substitution remain open. Four parent interfaces match failed/unaccepted Full114 and two candidate dependencies have exact pins. No local Lean or Lake ran.

Remaining to-do list: authoritative kernel/axiom/warning verification, row-coordinate posterior score transport and numeric margins, legitimate decoder/source NO, common base/runtime, replay and all mandatory independent/final certification gates.

V2 is a single proof-side repair: add the explicit ambient finrank identity from the actual row-coordinate linear equivalence before the natural-number dimension arithmetic. Public declarations, their statements, imports, options and Checks are unchanged. Removing the added identity reverses exactly to captured V1. Neither source is compiled or accepted.
