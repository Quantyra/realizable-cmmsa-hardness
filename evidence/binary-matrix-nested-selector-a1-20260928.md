# Exact nested hybrid selector for A1

`BinaryMatrixNestedSelectorA1.selected_nested_iff` proves both directions of the manuscript's nested selector comparison for every finite binary source/codomain, every `A₂ ≤ A₁`, `B₁ ≤ B₂`, and every frequency `Y : W → V`. The intermediate selector uses the canonical quotient `V/A₂`, the subtype `B₂`, and the submodule maps `A₁.map A₂.mkQ` and `B₁.comap B₂.subtype`. No complement or basis is chosen.

This is the selector component of manuscript (A1), not the full function-level derivative identity. The next required theorem composes Fourier filters with affine restriction and proves the phase/base equality at `T + j_{B₂} S q_{A₂}` for arbitrary actual bases `S,T`.

The quotient/inclusion carrier factorization is already proved at satellite commit `449c87d` in `BinaryMatrixActualAffineCarrier.mem_fibre_iff_exists_carrierMap`; this supersedes the older A15 evidence note that listed factorization as open.

The selector result is a prerequisite to the A1 fourth-moment induction. It does not reduce the numerical NO-soundness gap: the full A1, A22, and MZ decoder remain open.
