# Binary matrix line translation: exact A14 boundary

Story: `stories/S3132-realizable-hardness-outer-game-and-star-pcp.md`.
Manuscript source: `paper/body.tex`, Appendix A, (A13)–(A14).

`BinaryMatrixLineTranslation.lean` defines the manuscript's order-one
translation average for the final codomain line: choose a functional with
final coordinate one uniformly, choose an independent uniform domain shift,
and translate the matrix by their rank-one product. It also defines
`P_{j+1}=(I-2^{j+1}E)(I-2^j E)` for every `j≥0`. This successor indexing
represents manuscript `P_k` only at `k=j+1`; the manuscript's `k≥1` guard
must still be supplied at each use.

The Lean proofs establish, for all finite dimensions including zero, that
every character is an eigenfunction of this *actual* average. The eigenvalue
is precisely the fraction of final-coordinate-one functionals in the kernel
of the frequency matrix. The row-shift average has been eliminated by binary
character orthogonality. For every hybrid-selected frequency, that fraction
is zero, matching the selected branch of (A13).

The unselected branch of (A13) is now proved in
`affineKernelFraction_eq_invTwo_pow_rank_of_not_hybridLineSelected`:

```lean
∀ {n d : ℕ} (Y : BinaryMatrix n (d + 1)),
  ¬ hybridLineSelected Y →
    affineKernelFraction Y = ((2 : ℝ)⁻¹) ^ Y.rank
```

It counts the affine fiber
`{φ : Fin d → ZMod 2 | Y.mulVec (Fin.snoc φ 1) = 0}` as
`2^(d-rank Y)` out of `2^d` choices. The proof derives a kernel vector with
final coordinate one from the nonselected row-space condition, translates the
affine fiber to the shortened matrix's kernel, and applies rank-nullity and
the finite-field vector-space cardinality theorem. The selected branch above
proves no such vector exists when the hybrid selector holds. Thus
`lineTranslationMultiplier_eq_hybrid` establishes both character multipliers
of (A13) for the actual average.

The first remaining comparison is the full (A13) function identity at a
fixed input rank, followed by the (A14) output rank projection. The latter
must aggregate Fourier collisions after raw restriction on the reduced
matrix space. The source theorem `lineTranslationAverage_character_explicit`
is only a character eigenvalue statement; it is not yet the full (A13) or
(A14) identity for arbitrary functions. No A14 or A22 claim is made here,
and this result does not reduce the numeric NO-soundness gap.
