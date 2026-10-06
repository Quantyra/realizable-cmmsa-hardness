import PvNP.RealizableHardness.BinaryMatrixA1Complex
import PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneSelector
import PvNP.RealizableHardness.BinaryMatrixTypedA14Hyperplane
import PvNP.RealizableHardness.BinaryMatrixCodomainA14
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A18TransposeTransport
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exact transpose covariance of the ambient hybrid selector and its
complex Fourier filter. The codomain constraint is transported to the
coordinate dual annihilator in the transposed domain. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17TransposeHybridFilter

open BinaryMatrixFourier BinaryMatrixNestedSelectorA1 BinaryMatrixA1Complex
open BinaryMatrixTypedHyperplaneSelector BinaryMatrixTypedA14Hyperplane
open BinaryMatrixCodomainA14 BinaryMatrixComplexA15
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (n : Nat) := Fin n → F

private def dualCoordinateEquiv (n : Nat) :
    Module.Dual F (V n) ≃ₗ[F] V n :=
  (Pi.basisFun F (Fin n)).dualBasis.equivFun

/-- Vector realization of the linear-functional annihilator under the
standard coordinate duality. -/
def coordinateDualAnnihilator {n : Nat}
    (B : Submodule F (V n)) : Submodule F (V n) :=
  B.dualAnnihilator.map (dualCoordinateEquiv n).toLinearMap

/-- The coordinate dual annihilator has the expected complementary
dimension. -/
theorem coordinateDualAnnihilator_finrank {n : Nat}
    (B : Submodule F (V n)) :
    Module.finrank F (coordinateDualAnnihilator B) +
      Module.finrank F B = Module.finrank F (V n) := by
  rw [coordinateDualAnnihilator, (dualCoordinateEquiv n).finrank_map_eq]
  simpa only [Nat.add_comm] using
    (Subspace.finrank_add_finrank_dualAnnihilator_eq B)

/-- A codimension-one codomain constraint becomes a one-dimensional
fixed-domain subspace under transpose. -/
theorem coordinateDualAnnihilator_finrank_one {n : Nat}
    (B : Submodule F (V n))
    (hB : Module.finrank F ((V n) ⧸ B) = 1) :
    Module.finrank F (coordinateDualAnnihilator B) = 1 := by
  have hdim := coordinateDualAnnihilator_finrank B
  have hquot := B.finrank_quotient_add_finrank
  rw [hB] at hquot
  omega

private theorem dualMap_coordinates {r c : Nat}
    (M : BinaryMatrix r c) (φ : Module.Dual F (V r)) :
    (dualCoordinateEquiv c) (M.mulVecLin.dualMap φ) =
      M.transpose.mulVec ((dualCoordinateEquiv r) φ) := by
  funext i
  simp only [dualCoordinateEquiv, Module.Basis.dualBasis_equivFun,
    Pi.basisFun_apply]
  simp only [LinearMap.dualMap_apply, Matrix.mulVec, dotProduct,
    Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_single_one]
  conv_lhs => rw [← (Pi.basisFun F (Fin r)).sum_repr (Matrix.col M i)]
  simp [map_sum, map_smul, Pi.basisFun_repr]

/-- The row-space/range identity in coordinate dual form. -/
private theorem range_eq_coordinateDualAnnihilator_ker {n d : Nat}
    (Y : BinaryMatrix n d) :
    LinearMap.range Y.mulVecLin =
      (LinearMap.ker Y.transpose.mulVecLin).dualAnnihilator.map
        (dualCoordinateEquiv n).toLinearMap := by
  classical
  let eN := dualCoordinateEquiv n
  let eD := dualCoordinateEquiv d
  let f := Y.transpose.mulVecLin
  have hcoord (φ : Module.Dual F (V d)) :
      eN (f.dualMap φ) = Y.mulVecLin (eD φ) := by
    change eN (Y.transpose.mulVecLin.dualMap φ) =
      Y.mulVec (eD φ)
    exact dualMap_coordinates Y.transpose φ
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    have hphi : f.dualMap (eD.symm v) ∈
        (LinearMap.ker f).dualAnnihilator := by
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      exact ⟨eD.symm v, rfl⟩
    refine ⟨f.dualMap (eD.symm v), hphi, ?_⟩
    change eN (f.dualMap (eD.symm v)) = Y.mulVecLin v
    simpa only [LinearEquiv.apply_symm_apply] using hcoord (eD.symm v)
  · rintro ⟨phi, hphi, hx⟩
    have hphirange : phi ∈ LinearMap.range f.dualMap := by
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      exact hphi
    rcases hphirange with ⟨psi, hpsi⟩
    have hval : Y.mulVecLin (eD psi) = x := by
      rw [← hcoord psi, hpsi]
      change eN phi = x
      exact hx
    exact ⟨eD psi, hval⟩

/-- The raw affine transpose chooses exactly the coordinate dual
annihilator as its fixed domain. -/
theorem transposeActualRestriction_domainFixed_eq_coordinateDualAnnihilator
    {n d : Nat} (Q : BinaryMatrixActualAffine.ActualAffineRestriction n d) :
    (ActualBinaryMatrixHC46A18TransposeTransport.transposeActualRestriction Q).domainFixed =
      coordinateDualAnnihilator Q.codomainVariation := by
  have h := range_eq_coordinateDualAnnihilator_ker
    ((BinaryMatrixActualAffine.rawOfActual Q).leftDirections.transpose)
  unfold ActualBinaryMatrixHC46A18TransposeTransport.transposeActualRestriction
    BinaryMatrixActualAffine.actualOfRaw BinaryMatrixCodomainA15.transposeRaw
  rw [← BinaryMatrixActualAffine.rawOfActual_left_kernel Q]
  unfold coordinateDualAnnihilator
  simpa only [Matrix.transpose_transpose] using h

/-- A frequency is selected by the bottom-domain/codomain-`B` hybrid rule
iff its transpose is selected by the line of functionals annihilating `B`.
This is the generic subspace statement, not just the hyperplane case. -/
private theorem toLin'_eq_mulVecLin {n d : Nat} (Y : BinaryMatrix n d) :
    Y.toLin' = Y.mulVecLin := by
  ext x
  rfl

theorem selected_bot_iff_coordinateDualAnnihilator_top {n d : Nat}
    (B : Submodule F (V n)) (Y : BinaryMatrix n d) :
    Selected (⊥ : Submodule F (V d)) B Y.transpose.toLin' ↔
    Selected (coordinateDualAnnihilator B)
        (⊤ : Submodule F (V d)) Y.toLin' := by
  rw [toLin'_eq_mulVecLin Y.transpose, toLin'_eq_mulVecLin Y]
  unfold Selected
  rw [range_eq_coordinateDualAnnihilator_ker Y]
  constructor
  · rintro ⟨_, hpre⟩
    have hker : LinearMap.ker Y.transpose.mulVecLin ≤ B := by
      intro x hx
      exact hpre x ((LinearMap.mem_ker).mp hx)
    constructor
    · intro x hx
      rcases hx with ⟨φ, hφ, rfl⟩
      exact ⟨φ, Submodule.dualAnnihilator_anti hker hφ, rfl⟩
    · intro x _
      exact Submodule.mem_top
  · rintro ⟨hrange, _⟩
    constructor
    · exact bot_le
    · intro x hx
      have hker : x ∈ LinearMap.ker Y.transpose.mulVecLin :=
        (LinearMap.mem_ker).mpr hx
      have hdual : B.dualAnnihilator ≤
          (LinearMap.ker Y.transpose.mulVecLin).dualAnnihilator := by
        intro φ hφ
        have hmap : dualCoordinateEquiv n φ ∈
            (LinearMap.ker Y.transpose.mulVecLin).dualAnnihilator.map
              (dualCoordinateEquiv n).toLinearMap := hrange ⟨φ, hφ, rfl⟩
        rcases hmap with ⟨ψ, hψ, hEq⟩
        exact (dualCoordinateEquiv n).injective hEq ▸ hψ
      exact (Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp hdual) hker

/-- The ambient complex hybrid filter commutes exactly with transposition
when the codomain constraint is transported to its coordinate dual
annihilator. -/
theorem complexAmbientHybridFilter_transpose_bot {n d : Nat}
    (B : Submodule F (V n)) (f : BinaryMatrix n d → Complex)
    (M : BinaryMatrix d n) :
    complexTranspose (complexAmbientHybridFilter
        (⊥ : Submodule F (V d)) B f) M =
      complexAmbientHybridFilter (coordinateDualAnnihilator B)
        (⊤ : Submodule F (V d)) (complexTranspose f) M := by
  classical
  let e : BinaryMatrix n d ≃ BinaryMatrix d n := {
    toFun := Matrix.transpose
    invFun := Matrix.transpose
    left_inv := Matrix.transpose_transpose
    right_inv := Matrix.transpose_transpose
  }
  unfold complexTranspose complexAmbientHybridFilter
  rw [← Equiv.sum_comp e
    (fun Z : BinaryMatrix d n =>
      if Selected (coordinateDualAnnihilator B) (⊤ : Submodule F (V d))
          Z.transpose.toLin' then
        complexFourierCoeff (fun X => f X.transpose) Z *
          (character Z M : Complex) else 0)]
  apply Finset.sum_congr rfl
  intro Y _
  have he : e Y = Y.transpose := rfl
  simp only [he, Matrix.transpose_transpose]
  rw [selected_bot_iff_coordinateDualAnnihilator_top]
  by_cases hY : Selected (coordinateDualAnnihilator B)
      (⊤ : Submodule F (V d)) Y.toLin'
  · simp only [if_pos hY]
    rw [← complexFourierCoeff_transpose]
    rw [← character_transpose Y M.transpose, Matrix.transpose_transpose]
    rfl
  · simp only [if_neg hY]

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17TransposeHybridFilter
