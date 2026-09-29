# Canonical nested carrier and affine base for A1

`BinaryMatrixA1NestedCarrier` proves the actual nested affine carrier identification for every `A₂≤A₁≤V` and `B₁≤B₂≤W`: `((V/A₂)/(A₁/A₂)) ≃ V/A₁`, `(B₁ inside B₂) ≃ B₁`, and the induced equivalence between their Hom spaces. `nestedCarrier_apply_mk` checks the canonical quotient map on every original vector, without choosing complements.

`nestedCarrier_affine_base` proves the exact displacement identity for arbitrary actual bases `T:V→W`, `S:V/A₂→B₂`, and later carrier map `N`:

`T + j_B₂ (S + j_(B₁⊆B₂) N q_(A₁/A₂)) q_A₂ = (T + j_B₂ S q_A₂) + j_B₁ (transport N) q_A₁`.

This is force-bearing infrastructure for manuscript (A1). The full function-level hybrid derivative identity remains unproved: it needs the filtered Fourier coefficient transfer through the first restriction, followed by the nested selector iff on the transported frequency. The numerical NO-soundness gap is unchanged.
