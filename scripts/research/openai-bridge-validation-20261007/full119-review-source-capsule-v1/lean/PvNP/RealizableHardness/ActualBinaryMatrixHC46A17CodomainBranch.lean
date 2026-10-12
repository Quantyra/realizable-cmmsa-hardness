import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentEnergy
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainFrequencyCovariance
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A17TransposeHybridFilter
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18CodomainNormalEnergy
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalEnergy
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18EnergyTriangle
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeAverage
import PvNP.RealizableHardness.BinaryMatrixCodomainA14
import PvNP.RealizableHardness.BinaryMatrixComplexA14
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The codomain-nonfull branch of A17. A nonzero functional annihilating
the parent's codomain defines a containing hyperplane. Transposition
identifies its coordinate dual line with a direction in the transposed
parent. The derivative bound stays on the original `(bottom, hyperplane)`
carrier; only the A13 decomposition and A18 average are transported. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17CodomainBranch

open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17GenericParentEnergy
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DerivativeCoordinate
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17DomainFrequencyCovariance
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A17TransposeHybridFilter
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18CodomainNormalEnergy
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18FullFunctionalEnergy
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18EnergyTriangle
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeAverage
open PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeTransport
open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixActualAffine
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualTypedABCanonicalDCollapse
open PvNP.RealizableHardness.BinaryMatrixCodomainA14
open PvNP.RealizableHardness.BinaryMatrixComplexA14

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

private def dualCoordinateEquiv (n : Nat) :
    Module.Dual F (V n) ≃ₗ[F] V n :=
  (Pi.basisFun F (Fin n)).dualBasis.equivFun

private theorem complexRankProjection_transpose {n d j : Nat}
    (f : BinaryMatrix n d → Complex) :
    complexTranspose (complexRankProjection j f) =
      complexRankProjection j (complexTranspose f) := by
  funext M
  apply Complex.ext
  · simp only [complexTranspose, complexRankProjection_re]
    exact (BinaryMatrixCodomainA14.rankProjection_transpose
      (fun X => (f X).re) M.transpose).symm
  · simp only [complexTranspose, complexRankProjection_im]
    exact (BinaryMatrixCodomainA14.rankProjection_transpose
      (fun X => (f X).im) M.transpose).symm

/-- A17's codomain-hyperplane branch for an exact-order parent with
trivial fixed domain. The order-one derivative premise is used at the
original bottom-domain/codomain-hyperplane carrier. -/
theorem actual_A17_codomain_branch
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
    (hPdomain : P.domainFixed = ⊥) :
    fibreEnergy P.fibre f ≤ 2 * η₁ + 4 * (2 : Real) ^ (2 * D) * η₂ := by
  classical
  have hPformula := actualAffineRestriction_order_formula P
  rw [hPdomain, finrank_bot] at hPformula
  change P.order = 0 + Module.finrank F (W n ⧸ P.codomainVariation) at hPformula
  have hcodim : Module.finrank F (W n ⧸ P.codomainVariation) = r := by
    simpa only [Nat.zero_add, hPorder] using hPformula.symm
  have hdualrank := coordinateDualAnnihilator_finrank P.codomainVariation
  change Module.finrank F (coordinateDualAnnihilator P.codomainVariation) +
      Module.finrank F P.codomainVariation = Module.finrank F (W n) at hdualrank
  have hquot := P.codomainVariation.finrank_quotient_add_finrank
  change Module.finrank F (W n ⧸ P.codomainVariation) +
      Module.finrank F P.codomainVariation = Module.finrank F (W n) at hquot
  rw [hcodim] at hquot
  have hdual_dim :
      Module.finrank F (coordinateDualAnnihilator P.codomainVariation) = r := by
    omega
  have hdual_ne_bot : coordinateDualAnnihilator P.codomainVariation ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdual_dim
    omega
  obtain ⟨u, huDual, hu⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hdual_ne_bot
  let e := dualCoordinateEquiv n
  have huMap : u ∈ P.codomainVariation.dualAnnihilator.map e.toLinearMap := by
    change u ∈ P.codomainVariation.dualAnnihilator.map e.toLinearMap at huDual
    exact huDual
  rcases Submodule.mem_map.mp huMap with ⟨φ, hφ, hφu⟩
  have hφeq : φ = e.symm u := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact hφu
  have hφ : e.symm u ∈ P.codomainVariation.dualAnnihilator := by
    rw [← hφeq]
    exact hφ
  have hφ_ne : e.symm u ≠ 0 := by
    intro hzero
    apply hu
    have h := congrArg e hzero
    simpa only [map_zero, e.apply_symm_apply] using h
  let B : Submodule F (W n) := LinearMap.ker (e.symm u)
  have hPcod : P.codomainVariation ≤ B := by
    intro y hy
    change (e.symm u) y = 0
    exact (Submodule.mem_dualAnnihilator (e.symm u)).mp hφ y hy
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hφ_ne
  change Module.finrank F (LinearMap.ker (e.symm u)) + 1 = Module.finrank F (W n) at hker
  have hBquot := B.finrank_quotient_add_finrank
  change Module.finrank F (W n ⧸ B) + Module.finrank F B = Module.finrank F (W n) at hBquot
  have hBdim : Module.finrank F (W n ⧸ B) = 1 := by
    have hkerB : Module.finrank F B + 1 = Module.finrank F (W n) := hker
    omega
  have hBdual : e.symm u ∈ B.dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator (e.symm u)).2
    intro y hy
    exact LinearMap.mem_ker.mp hy
  have huB : u ∈ coordinateDualAnnihilator B := by
    change u ∈ B.dualAnnihilator.map e.toLinearMap
    exact ⟨e.symm u, hBdual, e.apply_symm_apply u⟩
  let U : Submodule F (V n) := Submodule.span F ({u} : Set (V n))
  have hUdim : Module.finrank F U = 1 := by
    simpa [U] using (finrank_span_singleton hu)
  have hUleB : U ≤ coordinateDualAnnihilator B :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr huB
  have hBdual_dim := coordinateDualAnnihilator_finrank_one B hBdim
  have hUeq : U = coordinateDualAnnihilator B :=
    Submodule.eq_of_le_of_finrank_eq hUleB (hUdim.trans hBdual_dim.symm)
  let PT := transposeActualRestriction P
  have hPTdomain :=
    transposeActualRestriction_domainFixed_eq_coordinateDualAnnihilator P
  have hUlePT : U ≤ PT.domainFixed := by
    rw [hPTdomain]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr huDual
  have hcost : Module.finrank F (⊥ : Submodule F (V d)) +
      Module.finrank F (W n ⧸ B) = 1 := by
    rw [finrank_bot, hBdim]
  have hderivBot : ∀ T : V d →ₗ[F] W n,
      UpToActualNormSqGlobal (r - 1) η₁
        (actualDerivativeCoordinate (⊥ : Submodule F (V d)) B T f) := by
    intro T
    exact hderiv (⊥ : Submodule F (V d)) B T hcost
  have hcomponent : fibreEnergy P.fibre
      (complexAmbientHybridFilter (⊥ : Submodule F (V d)) B f) ≤ η₁ :=
    actual_derivative_bounds_every_parent_unit_cost
      (⊥ : Submodule F (V d)) B f hderivBot P bot_le hPcod hcost hPorder
  have hsourceOrder : P.order ≤ (r - 1) + 1 := by omega
  have haverage : fibreEnergy P.fibre
      (actualA18TransposeAverage u f) ≤ 2 * η₂ := by
    exact actualA18_parent_fibre_energy_le_two_codomain_normal
      f hsource P hsourceOrder ⟨u, by
        rw [hPTdomain]
        exact huDual⟩ hu
  have hPBase : P.base ∈ P.fibre := actual_fibre_base_mem P
  have hcard : (0 : Real) < P.fibre.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨P.base, hPBase⟩
  have hDtrans : complexRankProjection D (complexTranspose f) =
      complexTranspose f := by
    have h := congrArg complexTranspose hD
    rw [complexRankProjection_transpose] at h
    exact h
  have hcoef : (2 : Complex) ^ D = Complex.ofReal ((2 : Real) ^ D) := by
    exact (Complex.ofReal_pow (2 : Real) D).symm
  have hdouble : complexTranspose (complexTranspose f) = f := by
    funext M
    simp only [complexTranspose, Matrix.transpose_transpose]
  have hfilter (M : BinaryMatrix n d) :
      complexAmbientHybridFilter U (⊤ : Submodule F (W d))
          (complexTranspose f) M.transpose =
        complexAmbientHybridFilter (⊥ : Submodule F (V d)) B f M := by
    have h := complexAmbientHybridFilter_transpose_bot B f M.transpose
    rw [← hUeq] at h
    simpa only [complexTranspose, Matrix.transpose_transpose] using h.symm
  have havgpoint (M : BinaryMatrix n d) :
      actualA18Average u (complexTranspose f) M.transpose =
        actualA18TransposeAverage u f M := by
    have h := complexTranspose_actualA18Average u (complexTranspose f) M
    rw [hdouble] at h
    simpa only [complexTranspose, Matrix.transpose_transpose] using h
  have hdecomp : ∀ M ∈ P.fibre,
      f M = complexAmbientHybridFilter (⊥ : Submodule F (V d)) B f M +
        Complex.ofReal ((2 : Real) ^ D) * actualA18TransposeAverage u f M := by
    intro M hM
    have hA13 := homogeneous_A13_arbitrary_line u hu
      (complexTranspose f) hDtrans M.transpose
    calc
      f M = complexTranspose f M.transpose := rfl
      _ = complexAmbientHybridFilter U (⊤ : Submodule F (W d))
            (complexTranspose f) M.transpose +
          (2 : Complex) ^ D *
            actualA18Average u (complexTranspose f) M.transpose := hA13
      _ = complexAmbientHybridFilter (⊥ : Submodule F (V d)) B f M +
          Complex.ofReal ((2 : Real) ^ D) * actualA18TransposeAverage u f M := by
        rw [hfilter M, havgpoint M, hcoef]
  have htriangle := actual_fibre_energy_add_smul_le P f
    (complexAmbientHybridFilter (⊥ : Submodule F (V d)) B f)
    (actualA18TransposeAverage u f) (c := (2 : Real) ^ D) (by positivity)
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
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17CodomainBranch
