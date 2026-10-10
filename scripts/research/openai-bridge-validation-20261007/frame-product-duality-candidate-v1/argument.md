S3137 successor to qualified Full105: exact product-form energy.

Reuse the complete reviewed exact-operator argument and the qualified same-image
energy law. This candidate translates its frame-ratio/product step; it does not
claim G/Phi composition, adjoint, complex generality, source witnesses or runtime.
All Full105 sources and its three-lens acceptance remain immutable.

Write G(n,k) for the natural ordered-frame product. Splitting its Fin product at
the last index gives G(n,k+1)=G(n,k)(2^n-2^k). Splitting at index zero and factoring
2 from every remaining factor gives
G(n+1,k+1)=(2^(n+1)-1)2^k G(n,k).
Both identities hold with zero factors; natural multiplication distributes over
natural subtraction without a hidden nontruncation premise.

For s<=n+1, combine those recurrences and
2^(n+1)-2^s=2^s(2^(n+1-s)-1), cancelling the positive 2^s. This proves the width
shift G(n+1,s)(2^(n+1-s)-1)=G(n,s)(2^(n+1)-1).

Induct on i with c variable to prove
G(c,i)G(c+s,s)=G(c+s,i)G(c+s-i,s), assuming i<=c+s.
At i=0 both sides coincide. At i+1,c=0 the numerator and the dual frame count
both have a genuine zero factor. At i+1,c+1 use the diagonal recurrence on both
rank counts, the width shift for s, and the induction hypothesis at c,i.
This is a counted equality, not a assumed ratio or a retained-rank restriction.

G(c+s,i) and G(c+s,s) are positive. Cast and divide the equality to obtain
G(c,i)/G(c+s,i)=G(c+s-i,s)/G(c+s,s).
For i<=c the products can be cast factor by factor because j<s<=c+s-i.
For i>c, casting truncated factors individually would be invalid: instead use
the zero factor j=c+s-i<s in the real product and the zero natural frame count.
This yields the exact s-factor product in both cases, including s=0 and c=0.

Apply the qualified Full105 unconditional-append energy law directly and rewrite
its ratio. The statement keeps arbitrary invariant real F, paired inverses,
rank i<=c+s and separately normalized carriers. No Booleanity, source-height,
rank filter on sampled data or new analytic premise is introduced.

The i<=c+s guard is essential to ratio duality: with s=0 and i>c the first ratio
is zero under Lean's total division, while the empty s-product is one. Finite
enumeration is a bounded smoke check only. GCP kernel/axiom/warning evidence,
full dependency trace and independent material review remain required.
