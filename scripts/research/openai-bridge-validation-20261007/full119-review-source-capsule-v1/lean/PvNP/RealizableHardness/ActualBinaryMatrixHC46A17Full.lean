import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainBranch
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17CodomainBranch

/-! The full exact-order A17 parent bound. Split on the parent's fixed
domain: a nonzero domain uses the domain-line branch; a zero domain and
positive exact order forces a proper codomain and uses the codomain
hyperplane branch. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17Full

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainBranch
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17CodomainBranch
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixComplexA14

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- Every exact-order-r affine parent satisfies the A17 energy estimate,
from the original global source and universal original order-one derivative
premises alone. -/
theorem actual_A17_full_parent_energy
    {n d r D : Nat} {η₁ η₂ : Real}
    (f : BinaryMatrix n d → Complex)
    (hsource : UpToActualNormSqGlobal (r - 1) η₂ f)
    (hderiv : ∀ (A : Submodule F (V d)) (B : Submodule F (W n))
      (T : V d →ₗ[F] W n),
        Module.finrank F A + Module.finrank F (W n ⧸ B) = 1 →
        UpToActualNormSqGlobal (r - 1) η₁
          (actualDerivativeCoordinate A B T f))
    (hD : complexRankProjection D f = f)
    (hDpos : 1 ≤ D) (hr : 1 ≤ r)
    (P : ActualAffineRestriction n d)
    (hPorder : P.order = r) :
    fibreEnergy P.fibre f ≤ 2 * η₁ + 4 * (2 : Real) ^ (2 * D) * η₂ := by
  classical
  by_cases hPdomain : P.domainFixed = ⊥
  · exact actual_A17_codomain_branch f hsource hderiv hD hDpos hr P hPorder hPdomain
  · exact actual_A17_domain_branch f hsource hderiv hD hDpos hr P hPorder hPdomain

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17Full
