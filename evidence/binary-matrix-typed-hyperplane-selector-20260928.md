# Typed hyperplane selector identification

`BinaryMatrixTypedHyperplaneSelector.lean` identifies the coordinate selector used by typed hyperplane A14 with the intrinsic manuscript condition, for every finite binary ambient space, quotient input, codimension-one submodule `H` of the output carrier `B`, and frequency `Y : B →ₗ[ZMod 2] V/A`:

`typedHyperplaneSelected B H hH Y ↔ ker Y ≤ H`.

It also identifies this with membership of the defining functional `ψ` in `range Y.dualMap`. The proof transports the finite coordinate selector through the adapted output basis and the domain quotient basis. It does not assume positive input dimension or a nonzero frequency.

Targeted Lake build: `lake build PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneSelector` succeeded (2306 jobs). The companion Checks module records theorem types and axioms.

This closes the selector boundary needed to match manuscript A13/A14 hyperplane selection. It does not prove typed A1 iteration, an MZ NO decoder, original verifier source-law transfer, or any improved NO-soundness exponent. Numerical NO-gap effect: none yet.
