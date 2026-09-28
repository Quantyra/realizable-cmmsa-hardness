# Binary matrix line translation: exact A14 boundary

Story: `stories/S3132-realizable-hardness-outer-game-and-star-pcp.md`.
Manuscript source: `paper/body.tex`, Appendix A, (A13)–(A14).

`BinaryMatrixLineTranslation.lean` defines the manuscript's order-one
translation average for the final codomain line: choose a functional with
final coordinate one uniformly, choose an independent uniform domain shift,
and translate the matrix by their rank-one product. It also defines
`P_{j+1}=(I-2^{j+1}E)(I-2^j E)`, so the manuscript's `j≥1` boundary is
explicit.

The Lean proofs establish, for all finite dimensions including zero, that
every character is an eigenfunction of this *actual* average. The eigenvalue
is precisely the fraction of final-coordinate-one functionals in the kernel
of the frequency matrix. The row-shift average has been eliminated by binary
character orthogonality. For every hybrid-selected frequency, that fraction
is zero, matching the selected branch of (A13).

The first missing theorem for the unselected branch of (A13) is:

```lean
∀ {n d : ℕ} (Y : BinaryMatrix n (d + 1)),
  ¬ hybridLineSelected Y →
    affineKernelFraction Y = ((2 : ℝ)⁻¹) ^ Y.rank
```

It must count the affine fiber
`{φ : Fin d → ZMod 2 | Y.mulVec (Fin.snoc φ 1) = 0}` as
`2^(d-rank Y)` out of `2^d` choices. Equivalently, one must first prove that
the nonselected row-space condition supplies a kernel vector with final
coordinate one, then use its translation bijection and rank-nullity to count
the fiber. The selected branch above proves no such vector exists when the
hybrid selector holds.

Without this unselected multiplier branch, neither the full (A13) identity
nor the polynomial action needed for (A14) is certified. The subsequent
raw-restriction rank projection must also aggregate Fourier collisions on
the reduced matrix space. No A14 or A22 claim is made here, and this result
does not reduce the numeric NO-soundness gap.
