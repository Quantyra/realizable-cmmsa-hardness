# Distinct advice coverage by exact Grassmann incidence

E002/S3137. The complete argument was recorded before translation at planning commit 50e29d8 in the numeric obligations note, section 2026-10-11 Distinct-advice incidence argument. This is an uncompiled source candidate, not a certified result.

For each a in Fin(r+1), goodAdvice is the finite set of actual Q admitting P with a+codim(P.W)=r and original agreement greater than e/2. A Q occurs once regardless of its number of decoded witnesses W,g. Membership is characterized with the exact existential; fractions are the actual card divided by card(Grass V a), nonnegative and at most one even for an empty ambient stratum.

Every leaf in the actual originalGoodZoomCover comes from an originallyGood candidate. Its Q belongs to goodAdvice and is contained in the leaf. Hence the zoom cover is contained in the union of the full upper cones of the distinct good Q. card_biUnion_le bounds this union by the sum of cone cardinalities; the pinned actual upperCount_eq computes each cone as gaussian(n-a,d-a). There is no attempted injection from multiple candidates to distinct Q.

For r<=d<=n, all relevant ambient Gaussian counts are positive. The pinned flag_product identity yields gaussian(n,a)*gaussian(n-a,d-a)=gaussian(n,d)*gaussian(d,a). Dividing, and multiplying by the actual number of distinct good Q, gives the exact incidence ratio. Summing proves mass(cover)<=sum_a goodAdviceFraction(a)*gaussian(d,a).

The final two theorems apply an explicit uniform numerical bound B on those actual gaussian(d,a) factors. Together with any actual strict cover-mass lower bound D, they give D/B<sum_a goodAdviceFraction(a). This B input is explicitly not yet discharged in this module. The successor must instantiate B=4*2^(d*d) from the concrete Gaussian theorem and D=originalDensity/(2m) from the finite-cover theorem, then specialize d=2h and average under the original complement law. The exact-budget pair is retained in each Q's membership. No random-history, source decoder or successful-complement conditioning is introduced.

Three project sources and four Mathlib source identities match the Full114 archive/manifest; the three new candidate dependencies are separately hash-pinned and uncompiled. Full114 was not accepted. Future GCP verification must rebind all dependencies to the accepted operator successor and retain every parent scope requirement. Eleven public theorem axiom requests and four definition checks are included. No local Lean/Lake execution occurred.

Remaining to-do list: concrete Gaussian specialization, cover/inverse/bad-mass integration and original-law dimension averaging; GCP kernel/axiom/warning verification; actual source decoder/NO, random-history, runtime and full certification.
