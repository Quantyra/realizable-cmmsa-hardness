# Fixed-base codomain-hyperplane A14 sibling

`BinaryMatrixCodomainA14.lean` proves the exact Fourier rank-projection identity for the same actual codomain-hyperplane polynomial and fixed row base as the A15 sibling. It first proves matrix transposition preserves the binary pairing, characters, Fourier coefficients, and rank projection; the last step transports the existing full final-column A14 theorem. This includes collision aggregation in the output Fourier projection, all dimensions and ranks (including rank zero), arbitrary source function and base.

The output derivative `hyperplaneDerivative` is the manuscript hybrid one-hyperplane derivative expressed through the transposed full-domain hybrid selector. The theorem is coordinate hyperplane/full-domain; arbitrary hyperplanes and subspaces require the remaining A1 coordinate transport and peeling.

Verification: targeted `lake build PvNP.RealizableHardness.BinaryMatrixCodomainA14Checks` passed. The theorem uses only Lean's standard axioms `[propext, Classical.choice, Quot.sound]` and no `sorry` or custom axiom. This A14 identity and the companion A15 witness are force-bearing prerequisites; neither alone reduces the numerical MZ NO-soundness gap, since full A15/A22 and the decoder are open.
