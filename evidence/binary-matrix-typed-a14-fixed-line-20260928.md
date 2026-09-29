# Full typed complex A14 for an arbitrary domain line and fixed base

`typed_A14_fixedLine` proves the manuscript A14 rank-level identity
on intrinsic typed carriers for every `A ≤ V`, `B ≤ W`, one-dimensional
`L ≤ V/A`, fixed affine base `T : Hom(V/A,B)`, complex function `f`,
rank `j`, and reduced map `N : Hom((V/A)/L,B)`:

The rank-`j` projection of the actual typed witness
`N ↦ P_j f(T+N∘q_L)` equals the selected-line hybrid derivative of
the rank-`j+1` projection of `f`, evaluated at `T+N∘q_L`.

The proof transports both intrinsic rank projections and the selected
line filter through the adapted basis. Complex Fourier coefficients,
trace characters, and ranks are preserved. The arbitrary base has a
free-column offset in reduced coordinates; exact translation covariance
of complex Fourier coefficients and rank projection removes that offset
without loss. The full reduced frequency sum aggregates collisions.

This closes the domain-line complex A14 identity together with the
previous typed domain-line A15 one-step globalness bound. Codomain
hyperplane analogues and peeling arbitrary hybrid constraints with
complex A1 remain open. The numeric NO-soundness gap is unchanged.

`lake build PvNP.RealizableHardness.BinaryMatrixTypedA14FixedBaseChecks`
passed (2300 jobs). Translation covariance and the typed A14 theorem
depend only on `[propext, Classical.choice, Quot.sound]`.
