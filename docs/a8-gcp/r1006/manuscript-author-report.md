# S3132 manuscript author report

Date: 2026-10-04 America/Los_Angeles

## Result

The authorized integrated authoring attempt at `a8_output_q_le_actual_predecessor_sum` did not produce a faithful Lean proof. No Lean, Lake, elan, compiler, GCP, Git write, formatter, or destructive command was run. No Lean source was edited, and the accepted helper count remains 2.

The exact remaining identity is the complete output-pair transport through the actual A9 predecessor carriers. In Lean-ready form, its required endpoint is the manuscript theorem itself (with the dependent predicates expanded):

```lean
theorem a8_output_q_le_actual_predecessor_sum
    {n d D : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (t : T1IndexTriple A B)
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (horder : a6Order t ≤ D) :
    let C := t1AmbientC t.C
    let H := t1AmbientH t.K
    let X := t1PullbackMap t
    let k := Module.finrank F (LinearMap.range X)
    typedUniformMean (fun T : V d →ₗ[F] W n =>
      a7HybridQ (a7OutputBinary t T f)) ≤
      (2 : Real) ^ (6 * D * k) *
        ∑ p :
          {A' : Submodule F (V d) // C ≤ A'} ×
          {B' : Submodule F (W n) // B' ≤ H},
          if p.1.1 ∩ (LinearMap.range X).comap C.mkQ = C ∧
              B' + (LinearMap.ker X).map H.subtype = H then
            let A0 : A9AmbientA0 (V d) p.1.1
                (Module.finrank F C) :=
              ⟨C, p.1.2, rfl⟩
            let B0 : A9AmbientB0 (W n) p.2.1
                (Module.finrank F (W n ⧸ H)) :=
              ⟨H, p.2.2, rfl⟩
            typedUniformMean (fun T : V d →ₗ[F] W n =>
              (typedW6OutputEnergy p.1.1 p.2.1
                (a9AmbientFinalMap p.1.1 p.2.1 A0 B0 X)
                (filteredCarrierFunction p.1.1 p.2.1 T f)) ^ 2)
          else 0
```

The decisive missing subidentity is the exact normalized equality/reindexing that sends the sum of **all positive output-pair classes** in `a7HybridQ (a7OutputBinary t T f)` through the T2 selector/complement bijection to the corresponding summands indexed by the actual `A'`, `B'`, and induced A9 map `a9AmbientFinalMap ...`. It must identify the nested selector and affine filter on each side, not only their selected frequencies or their character inputs. It must also retain the zero class and the affine-base mean normalization so that the displayed inequality follows with exactly `(2 : Real) ^ (6 * D * k)`.

## Dependency mapping

- `t1MapToTriple`, `t1TripleEquiv`, `t1AmbientC`, `t1AmbientH`, `t1PullbackMap`, and the image/kernel and quotient lemmas establish the canonical T1 data and the actual carrier maps. The accepted local coordinate transport in `ActualBinaryMatrixHC46A8OutputCoordinateTransport.lean` transports nested means once selector/filter subspaces and maps are already supplied.
- `t2_left_derivative_expansion`, `t2_right_derivative_expansion`, `t2_left_to_right`, `t2_right_to_left`, and `t2_complement_unique` give the frequency-level selector/complement correspondence. They do not identify the induced T2 selector/filter contribution with the required actual A9 `(A0, B0, X)` summand for every output-pair class.
- `a7_pair_shares_exhaust` includes all pair classes, while `a7_output_zero_share_eq_l2` and `a7_output_binary_l2_sq` identify only the zero-order output contribution. `a7_outer_hybrid_energy_sq_le_complement_shares` controls one selected outer hybrid by complement shares, but is not the missing equality/reindexing for the complete output `Q` and its averaged positive classes.
- `a9AmbientA8Energy` and `a9Ambient_A8_sum_partition` operate on actual fixed-final fibers and the exact normalized energy. Their partition is downstream of the missing output-pair-to-actual-predecessor transport; it cannot establish that transport on its own.
- The supported rank/window and rank-cost results can supply the exponent estimate after that transport. They do not supply the missing selector/filter identity or permit replacing it with a stronger premise.

This identity is necessary for the same S3132 definition of done because the route requires a bound for the complete `a7HybridQ` at the fixed T1 output over arbitrary supported complex `f`, summed over actual nested final pairs with the exact affine-base normalization. Dropping positive output-pair classes, using only the zero-order L2 term, or replacing actual carriers/maps by a contribution proxy would change the required manuscript argument. No such identity is present in the inspected interfaces, and inventing it or asserting it as a premise would not be a proof.

## Changed paths

- `docs/a8-gcp/r1006/manuscript-author-report.md` — added this report.

The two authorized Lean source/check paths are unchanged. No compilation or acceptance is claimed.
