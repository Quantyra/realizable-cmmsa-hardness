import PvNP.RealizableHardness.BinaryMatrixA15NestedLine

/-! The exact A1 carrier step used for the fixed-slice part of A17.

The derivative hypothesis is kept on the genuinely reduced carrier.  The
parent restriction is reconstructed through the nested-line equivalence, so
the chosen affine base and the normalized uniform fibre measure are both
preserved.  This module does not infer globalness of a quotient extension. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17FixedSlice

open PvNP.RealizableHardness.BinaryMatrixA15NestedLine
open PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixFourier

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- A reduced derivative slice of order at most `r - 1` transfers with its
exact normalized energy to the corresponding parent affine restriction.

Here `A0 ≤ A1` is the fixed domain slice (the manuscript's `U ≤ A`), and
`Q` is the further restriction on the quotient carrier.  The parent fibre
is `lineCanonicalRestriction ... Q`; its base is the canonical embedding of
`Q.base`. -/
theorem fixed_slice_reduced_energy_le
    {n d r : Nat} {η : Real}
    (A0 A1 : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A0 ≤ A1)
    (g : (((V d ⧸ A0) ⧸ A1.map A0.mkQ) →ₗ[F] B) → Complex)
    (hg : UpToReducedNormSqGlobal A0 B (A1.map A0.mkQ) (r - 1) η g)
    (Q : ReducedRestriction A0 B (A1.map A0.mkQ))
    (hQ : Q.order ≤ r - 1) :
    fibreEnergy (lineCanonicalRestriction B hA Q).fibre
      (fun M => g ((lineCanonicalEquiv A0 A1 B hA).symm M)) ≤ η := by
  rw [lineCanonical_energy B hA Q g]
  exact hg Q hQ

/-- The parent carrier and its quotient slice have identical order, so a
`r - 1` derivative-globalness bound applies directly to every such slice. -/
theorem fixed_slice_parent_order_eq
    {n d : Nat}
    (A0 A1 : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A0 ≤ A1)
    (Q : ReducedRestriction A0 B (A1.map A0.mkQ)) :
    (lineCanonicalRestriction B hA Q).order = Q.order :=
  lineCanonical_order B hA Q

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17FixedSlice
