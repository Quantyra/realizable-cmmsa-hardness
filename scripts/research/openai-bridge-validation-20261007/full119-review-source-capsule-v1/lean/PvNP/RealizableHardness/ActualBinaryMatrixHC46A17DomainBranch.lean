import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentEnergy
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainFrequencyCovariance
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18EnergyTriangle
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalEnergy
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeTransport
import PvNP.RealizableHardness.BinaryMatrixComplexA14

/-! The domain-nonzero branch of A17. The original order-one derivative
globalness premise supplies the selected line estimate, while the original
global source premise supplies the A18 average estimate on the same parent
fibre. The arbitrary-line A13 identity and the finite-fibre squared triangle
inequality combine them without a caller-supplied decomposition or energy
bound. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainBranch

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentEnergy
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainFrequencyCovariance
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18EnergyTriangle
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalEnergy
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeTransport
open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- A17's domain-line branch for an exact-order parent. The only inputs are
the original source-global and order-one actual derivative-global
hypotheses, the homogeneous rank-D premise, and the nonzero-domain case
condition. -/
theorem actual_A17_domain_branch
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
    (hPorder : P.order = r)
    (hPdomain : P.domainFixed ≠ ⊥) :
    fibreEnergy P.fibre f ≤ 2 * η₁ + 4 * (2 : Real) ^ (2 * D) * η₂ := by
  classical
  obtain ⟨v, hvP, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPdomain
  let U : Submodule F (V d) := Submodule.span F ({v} : Set (V d))
  have hUdim : Module.finrank F U = 1 := by
    simpa [U] using (finrank_span_singleton hv)
  have hU : U ≤ P.domainFixed :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvP
  have hcost : Module.finrank F U +
      Module.finrank F (W n ⧸ (⊤ : Submodule F (W n))) = 1 := by
    have htop := (⊤ : Submodule F (W n)).finrank_quotient_add_finrank
    rw [finrank_top] at htop
    omega
  have hderivU : ∀ T : V d →ₗ[F] W n,
      UpToActualNormSqGlobal (r - 1) η₁
        (actualDerivativeCoordinate U (⊤ : Submodule F (W n)) T f) := by
    intro T
    exact hderiv U (⊤ : Submodule F (W n)) T hcost
  have hcomponent :
      fibreEnergy P.fibre
        (complexAmbientHybridFilter U (⊤ : Submodule F (W n)) f) ≤ η₁ :=
    actual_derivative_bounds_every_parent_unit_cost
      U (⊤ : Submodule F (W n)) f hderivU P hU le_top hcost hPorder
  have hsourceOrder : P.order ≤ (r - 1) + 1 := by omega
  have haverage :
      fibreEnergy P.fibre (actualA18Average v f) ≤ 2 * η₂ :=
    actualA18_parent_fibre_energy_le_two_inside f hsource P hsourceOrder
      ⟨v, hvP⟩ hv
  have hbase : P.base ∈ P.fibre := actual_fibre_base_mem P
  have hcard : (0 : Real) < P.fibre.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨P.base, hbase⟩
  have hcoef : (2 : Complex) ^ D = Complex.ofReal ((2 : Real) ^ D) := by
    exact (Complex.ofReal_pow (2 : Real) D).symm
  have hdecomp : ∀ M ∈ P.fibre,
      f M = complexAmbientHybridFilter
          U (⊤ : Submodule F (W n)) f M +
        (Complex.ofReal ((2 : Real) ^ D)) * actualA18Average v f M := by
    intro M hM
    have h := homogeneous_A13_arbitrary_line v hv f hD M
    simpa only [U, hcoef] using h
  have htriangle := actual_fibre_energy_add_smul_le P f
    (complexAmbientHybridFilter U (⊤ : Submodule F (W n)) f)
    (actualA18Average v f) (c := (2 : Real) ^ D) (by positivity)
    hcard hdecomp hcomponent haverage
  calc
    fibreEnergy P.fibre f ≤
        2 * η₁ + 2 * ((2 : Real) ^ D) ^ 2 * (2 * η₂) := htriangle
    _ = 2 * η₁ + 4 * (2 : Real) ^ (2 * D) * η₂ := by
      have hpow : ((2 : Real) ^ D) ^ 2 = (2 : Real) ^ (2 * D) := by
        rw [← pow_mul, Nat.mul_comm D 2]
      rw [hpow]
      ring

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainBranch
