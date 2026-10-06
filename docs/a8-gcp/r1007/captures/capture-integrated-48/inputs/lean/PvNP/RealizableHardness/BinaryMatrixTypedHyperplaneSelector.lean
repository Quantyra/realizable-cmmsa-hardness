import PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneIntrinsicP
import PvNP.RealizableHardness.BinaryMatrixTypedA14Hyperplane
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneSelector

open BinaryMatrixTypedHyperplaneIntrinsicP
open BinaryMatrixTypedA14Hyperplane
open BinaryMatrixTypedA15Hyperplane BinaryMatrixTypedA15Transport
open BinaryMatrixFourier BinaryMatrixHybridSelector
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

private theorem dualMap_coordinates {r c : ℕ}
    (M : BinaryMatrix r c) (φ : Module.Dual F (Fin r → F)) :
    (Pi.basisFun F (Fin c)).dualBasis.equivFun (M.mulVecLin.dualMap φ) =
      M.transpose.mulVec ((Pi.basisFun F (Fin r)).dualBasis.equivFun φ) := by
  funext i
  simp only [Module.Basis.dualBasis_equivFun, Pi.basisFun_apply]
  simp only [LinearMap.dualMap_apply, Matrix.mulVec, dotProduct,
    Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_single_one]
  conv_lhs => rw [← (Pi.basisFun F (Fin r)).sum_repr (Matrix.col M i)]
  simp [map_sum, map_smul, Pi.basisFun_repr]

private theorem coordinate_selector_iff_dual_range {r c : ℕ}
    (M : BinaryMatrix r c) (i : Fin c) :
    Pi.single i (1 : F) ∈ LinearMap.range M.transpose.mulVecLin ↔
      LinearMap.proj i ∈ LinearMap.range M.mulVecLin.dualMap := by
  let ec := (Pi.basisFun F (Fin c)).dualBasis.equivFun
  let er := (Pi.basisFun F (Fin r)).dualBasis.equivFun
  have hproj : ec (LinearMap.proj i) = Pi.single i (1 : F) := by
    funext j
    simp [ec, Module.Basis.dualBasis_equivFun, Pi.basisFun_apply,
      LinearMap.proj_apply, Pi.single_apply, eq_comm]
  constructor
  · rintro ⟨v, hv⟩
    let φ := er.symm v
    refine ⟨φ, ec.injective ?_⟩
    change ec (M.mulVecLin.dualMap φ) = ec (LinearMap.proj i)
    rw [dualMap_coordinates, hproj]
    have hφv : er φ = v := er.apply_symm_apply v
    rw [hφv]
    exact hv
  · rintro ⟨φ, hφ⟩
    refine ⟨er φ, ?_⟩
    rw [← hproj]
    rw [← hφ]
    exact (dualMap_coordinates M φ).symm

private theorem coordinate_selector_iff_kernel {r c : ℕ}
    (M : BinaryMatrix r c) (i : Fin c) :
    Pi.single i (1 : F) ∈ LinearMap.range M.transpose.mulVecLin ↔
      LinearMap.ker M.mulVecLin ≤ LinearMap.ker (LinearMap.proj i) := by
  rw [coordinate_selector_iff_dual_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    exact (LinearMap.mem_ker).mpr (h x hx)
  · intro h x hx
    exact (LinearMap.mem_ker).mp (h hx)

/-- Intrinsic form of the codomain-hyperplane selector: a frequency's kernel
lies in H exactly when the defining functional factors through it. -/
theorem ker_le_hyperplane_iff_defining_in_dual_range {n d : ℕ}
    {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    LinearMap.ker Y ≤ H ↔
      hyperplaneDefiningFunctional B H hH ∈ LinearMap.range Y.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [Submodule.mem_dualAnnihilator]
  have hker := hyperplaneDefiningFunctional_ker B H hH
  constructor
  · intro h w hw
    have hwH : w ∈ H := h hw
    rw [← hker] at hwH
    exact (LinearMap.mem_ker).mp hwH
  · intro h w hw
    have hwker : w ∈ LinearMap.ker (hyperplaneDefiningFunctional B H hH) :=
      (LinearMap.mem_ker).mpr (h w hw)
    rwa [hker] at hwker

/-- The coordinate selector in typed hyperplane A14 is precisely the
manuscript's intrinsic condition that the frequency kernel lies in H. -/
theorem typedHyperplaneSelected_iff_ker_le {n d : ℕ}
    {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    typedHyperplaneSelected B H hH Y ↔ LinearMap.ker Y ≤ H := by
  let T := hyperplaneFrequencyEquiv B H hH Y
  let e := hyperplaneAdaptedEquiv B H hH
  let D := (domainBasis A).equivFun
  have hlin : T.transpose.mulVecLin =
      D.toLinearMap.comp (Y.comp e.symm.toLinearMap) := by
    simpa only [T, Matrix.toLin'_apply'] using
      (hyperplaneFrequency_toLin B H hH Y)
  have hcoord : typedHyperplaneSelected B H hH Y ↔
      LinearMap.ker T.transpose.mulVecLin ≤
        LinearMap.ker (LinearMap.proj (Fin.last (Module.finrank F H))) := by
    simpa only [typedHyperplaneSelected, hybridLineSelected, T,
      Matrix.transpose_transpose] using
      (coordinate_selector_iff_kernel T.transpose
        (Fin.last (Module.finrank F H)))
  rw [hcoord]
  constructor
  · intro h w hw
    have hwzero : Y w = 0 := (LinearMap.mem_ker).mp hw
    have hew : e w ∈ LinearMap.ker T.transpose.mulVecLin := by
      apply (LinearMap.mem_ker).mpr
      rw [hlin]
      simp [hwzero]
    have hlast : e w (Fin.last (Module.finrank F H)) = 0 :=
      (LinearMap.mem_ker).mp (h hew)
    have hψ : w ∈ LinearMap.ker (hyperplaneDefiningFunctional B H hH) := by
      exact (LinearMap.mem_ker).mpr hlast
    rwa [hyperplaneDefiningFunctional_ker] at hψ
  · intro h x hx
    have hxzero : D (Y (e.symm x)) = 0 := by
      have := (LinearMap.mem_ker).mp hx
      rw [hlin] at this
      exact this
    have hY : e.symm x ∈ LinearMap.ker Y := by
      apply (LinearMap.mem_ker).mpr
      exact D.injective (by simpa using hxzero)
    have hψ : e.symm x ∈ LinearMap.ker
        (hyperplaneDefiningFunctional B H hH) := by
      rw [hyperplaneDefiningFunctional_ker]
      exact h hY
    apply (LinearMap.mem_ker).mpr
    have hlast := (LinearMap.mem_ker).mp hψ
    simpa [hyperplaneDefiningFunctional, e] using hlast

theorem typedHyperplaneSelected_iff_defining_in_dual_range {n d : ℕ}
    {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    typedHyperplaneSelected B H hH Y ↔
      hyperplaneDefiningFunctional B H hH ∈ LinearMap.range Y.dualMap :=
  (typedHyperplaneSelected_iff_ker_le B H hH Y).trans
    (ker_le_hyperplane_iff_defining_in_dual_range B H hH Y)

end
end PvNP.RealizableHardness.BinaryMatrixTypedHyperplaneSelector
