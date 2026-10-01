import PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel

/-! Canonical finite-dimensional coordinates on binary quotients. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46QuotientCoordinates

set_option autoImplicit false
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [FiniteDimensional (ZMod 2) V]

/-- The quotient by a subspace has the canonical coordinates supplied by its
finite basis. -/
noncomputable def quotientCoordinateEquiv (U : Submodule (ZMod 2) V) :
    (V ⧸ U) ≃ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) (V ⧸ U)) → ZMod 2) :=
  (Module.finBasis (ZMod 2) (V ⧸ U)).equivFun

/-- Quotient dimension when the fixed subspace is a line. -/
theorem quotient_finrank_eq_finrank_sub_one
    (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 1) :
    Module.finrank (ZMod 2) (V ⧸ U) =
      Module.finrank (ZMod 2) V - 1 := by
  have h := U.finrank_quotient_add_finrank
  omega

/-- Coordinates on a quotient by a one-dimensional subspace, indexed by the
ambient dimension minus one. -/
noncomputable def lineQuotientCoordinateEquiv
    (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 1) :
    (V ⧸ U) ≃ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) V - 1) → ZMod 2) :=
  (Module.finBasisOfFinrankEq (ZMod 2) (V ⧸ U)
    (quotient_finrank_eq_finrank_sub_one U hU)).equivFun

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46QuotientCoordinates
