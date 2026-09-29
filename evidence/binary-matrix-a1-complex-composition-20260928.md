# Complex-valued manuscript A1 composition

`BinaryMatrixA1Complex.manuscript_A1_complex` proves the manuscript's complex-valued (A1) hybrid derivative composition for every finite binary `V=𝔽₂^d`, `W=𝔽₂^n`, nested `A₂≤A₁`, `B₁≤B₂`, arbitrary actual affine bases `T:V→W` and `S:V/A₂→B₂`, every function `f:Hom(V,W)→ℂ`, and every point on the nested quotient/subtype carrier. The right side has base `T+j_B₂ S q_A₂` and is transported canonically to `Hom(V/A₁,B₁)`.

Both ambient and typed hybrid filters are defined directly from normalized complex Fourier coefficients and the manuscript's selected frequencies. The coefficient re/im lemmas prove these direct complex coefficients split into the corresponding real coefficients; filter re/im lemmas then let `Complex.ext` apply the verified real-valued (A1) to each component. This closes the coefficient-field caveat left by the real-valued A1 proof at `3326050`. It includes zero dimensions, order-zero cases, and coalesced first-stage frequencies.

This establishes (A1) only. A22, positive-rank hypercontractivity, the fourth-moment induction, the MZ NO decoder, and the numeric NO-soundness gap remain open. The numeric gap is unchanged by A1 alone.
