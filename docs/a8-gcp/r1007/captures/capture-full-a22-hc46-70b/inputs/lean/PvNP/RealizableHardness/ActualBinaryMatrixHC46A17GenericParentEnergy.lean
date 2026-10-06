import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentCoverage
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeGlobalTransfer

/-! Apply the carrier derivative bound to an original parent restriction.
The universal original derivative hypothesis is specialized at the original
parent base; the carrier order is charged by the exact lift decomposition. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentEnergy

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentCoverage
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeGlobalTransfer
open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixA1Complex

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The arbitrary-endpoint derivative hypothesis controls the energy of
every original parent fibre whose domain and codomain endpoints admit a
one-unit carrier reduction. No parent-energy premise is assumed. -/
theorem actual_derivative_bounds_every_parent_unit_cost
    {n d r : Nat} {ε : Real}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → Complex)
    (hderiv : ∀ T : V d →ₗ[F] W n,
      UpToActualNormSqGlobal (r - 1) ε
        (actualDerivativeCoordinate A B T f))
    (P : ActualAffineRestriction n d)
    (hA : A ≤ P.domainFixed)
    (hB : P.codomainVariation ≤ B)
    (hcost : Module.finrank F A + Module.finrank F (W n ⧸ B) = 1)
    (hP : P.order = r) :
    fibreEnergy P.fibre (complexAmbientHybridFilter A B f) ≤ ε := by
  let Q := carrierOfParentAB A B P
  have hQ : Q.order ≤ r - 1 := by
    apply carrierOfParentAB_order_le A B P hA hB hcost
    omega
  have henergy := actual_derivative_bounds_lifted_parent_fibre
    A B (Matrix.toLin' P.base) f
    (hderiv (Matrix.toLin' P.base)) Q hQ
  have heq := lift_carrierOfParentAB_eq A B P hA hB
  simpa [Q, heq] using henergy

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentEnergy
