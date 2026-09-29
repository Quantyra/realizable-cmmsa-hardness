# A1 composition on canonical line and hyperplane carriers

`line_A1_selected_composition` and
`hyperplane_A1_selected_composition` specialize the complex manuscript
A1 identity to both carriers produced by an A15 one-step peel. The line
branch proves `B.comap B.subtype = ⊤`; the hyperplane branch proves
`(H.map B.subtype).comap B.subtype = H`. Explicit input equivalences
match A1's nested carrier to the canonical line and hyperplane carriers.
Their affine displacement laws identify the second-step argument with
`S + N ∘ q` or `S + H.subtype ∘ N`, respectively.

For arbitrary fixed ambient base `T`, current base `S`, complex input,
and reduced point, the resulting selected filter equals the ambient
derivative at the combined base
`T + B.subtype ∘ S ∘ q_A₂`. This establishes the exact function-level
A1 composition for either one-step carrier.

The recursive witness induction and assembly of the accumulated A15 factor
with the previously proved order-zero endpoint remain open. The original
verifier-to-tagged source-law transfer and the MZ decoder are separate open
obligations. The numeric NO-soundness gap is unchanged.

## Three-lens review

| Lens | Verdict | Evidence and limit |
|------|---------|--------------------|
| Build/audit | GO | Independent `lake build PvNP.RealizableHardness.BinaryMatrixA15A1CarrierChecks`: 2316 jobs; `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound` for both composition theorems. |
| Proof-adversarial | GO-WITH-NOTES | Arbitrary `T`, `S`, `f`, and reduced point are preserved. The result is a one-step function identity, not a recursive A15 bound. |
| Complexity | GO-WITH-NOTES | Canonical peel carriers match manuscript A1/A15; no rank or asymptotic conclusion follows yet. |
| Non-claims | GO-WITH-NOTES | The statement leaves recursive A15, original verifier source transfer, MZ decoder, and numeric NO soundness open. |
