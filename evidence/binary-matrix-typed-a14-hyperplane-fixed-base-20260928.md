# Typed codomain-hyperplane A14, fixed base

`BinaryMatrixTypedA14HyperplaneFixedBaseChecks` audits the exact complex
rank/selector identity on `Hom(V/A,B)` and reduced `Hom(V/A,H)`, where
`H ≤ B` has codimension one. The frequency equivalences preserve cyclic
trace pairing, rank, normalized complex Fourier coefficients, and full
rank projections. The selected-frequency filter sums over the entire typed
frequency carrier, so coincident induced frequencies are retained.

For every prescribed base `T`, input `f`, rank `j`, and reduced map `N`, the
theorem `typed_A14_fixedHyperplane` identifies rank-`j` projection of
`N ↦ typedHyperplaneP j f (T + H.subtype ∘ N)` with the adapted-row
selected-frequency filter of rank-`(j+1)` projection of `f` at that same
map. The proof uses the full complex coordinate A14 theorem and exact
affine translation phase, including arbitrary `T`.

The current `typedHyperplaneP` is defined by coordinate conjugation, and
the typed selector is defined through its adapted frequency equivalence.
Equality with a separately defined intrinsic uniform `E_H/P` operator is
still open. This result therefore closes the fixed-base A14 comparison for
those precise operators but is not yet the full manuscript hyperplane
branch. Iterated A15 peeling and the original post-padding verifier-law
handoff remain open. The numeric MZ NO-soundness gap is unchanged.
