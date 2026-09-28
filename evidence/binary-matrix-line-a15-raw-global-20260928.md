# Binary matrix A15 fixed-base raw-global estimate

Date: 2026-09-28 Pacific. S3132 force-bearing Appendix A13-A15 route.

`BinaryMatrixLineA15.lean` proves, for every finite `n,d,k`, nonnegative `ε`, real function `f` on the full binary matrix space, and **every fixed base column** `t`, that

```
UpToRawSquareGlobal (k+1) ε f
  → UpToRawSquareGlobal k (4 * 2^(4*(k+1)) * ε)
      (rawLastColumnRestrict t (lineP k f)).
```

`lineP` is the actual A13 polynomial `(I-2^(k+1)E)(I-2^k E)`, with the uniform line-translation average `E`. The theorem has the manuscript's A15 factor and keeps the same arbitrary fixed `t` as the A14 identity. It does not claim a selected rank or decoder conclusion; A14 supplies the rank identity separately.

The proof constructs a full affine restriction from every reduced raw restriction, fixing the final column while transporting **both** the existing right equations and left values. Its fibre is exactly the image under `rawLastColumn _ t`, with budget increased by one and identical normalized square mean, including empty and zero-dimensional cases. Every matrix translation pulls an affine fibre to another same-budget fibre with both value matrices adjusted. Finite-average Jensen then proves `E` contracts this quantified squared-globalness bound; the two polynomial factors give the stated constant.

**Quantifier limitation:** `UpToRawSquareGlobal` quantifies over all `AffineRestriction` structures of *nominal* budget at most the order. The manuscript phrases globalness in terms of actual affine restrictions and their order. The next exact theorem is a representation/identification showing that every nonempty raw fibre of nominal budget at most `r` has manuscript actual order at most `r` (or an equivalent actual restriction with the same uniform fibre), and that an exact-order `r` manuscript premise controls those lower-order fibres. No such implication is asserted here. Consequently this is a force-bearing conditional A15 comparison, not a completed manuscript A15 or positive-rank hypercontractivity theorem. The numeric NO-soundness gap is unchanged.

Verification: local `lake build PvNP.RealizableHardness.BinaryMatrixLineA15Checks` passed, 2217 jobs. `#print axioms upToRawSquareGlobal_A15_fixedBase` returned `[propext, Classical.choice, Quot.sound]`. No GCP builder or visible console was launched.
