import PvNP.RealizableHardness.BinaryMatrixSameRangeOrbit
import PvNP.RealizableHardness.ActualRankImageRightBasisInvariance

/-! Same-range matrix orbits, including deficient maps.
This candidate is not native qualified and does not construct Spectral47.
-/
namespace PvNP.RealizableHardness.BinaryMatrixRightOrbit
open PvNP.RealizableHardness.BinaryMatrixFourier
set_option autoImplicit false
noncomputable section

/-- The generic domain equivalence gives paired matrix inverses. -/
theorem same_range_matrix_right_orbit {n d : Nat}
    (M N : BinaryMatrix n d)
    (h : LinearMap.range (Matrix.toLin' M) = LinearMap.range (Matrix.toLin' N)) :
    ∃ U V : BinaryMatrix d d, U * V = 1 ∧ V * U = 1 ∧ N * U = M := by
  classical
  obtain ⟨ e, he ⟩ := BinaryMatrixSameRangeOrbit.same_range_right_orbit
    (Matrix.toLin' M) (Matrix.toLin' N) h
  let U : BinaryMatrix d d := LinearMap.toMatrix' e.toLinearMap
  let V : BinaryMatrix d d := LinearMap.toMatrix' e.symm.toLinearMap
  have huv : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hvu : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have hcomp : (Matrix.toLin' N).comp e.toLinearMap = Matrix.toLin' M := by
    apply LinearMap.ext
    intro x
    exact he x
  refine ⟨ U, V, ?_, ?_, ?_ ⟩
  · change LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp, huv, LinearMap.toMatrix'_id]
  · change LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp, hvu, LinearMap.toMatrix'_id]
  · have hmatrix := congrArg LinearMap.toMatrix' hcomp
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using hmatrix

/-- All-matrix right-basis invariance forces equal values on equal images. -/
theorem basis_invariant_eq_of_same_range {n d : Nat} {A : Type*}
    (F : BinaryMatrix n d → A)
    (hInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (M N : BinaryMatrix n d)
    (h : LinearMap.range (Matrix.toLin' M) = LinearMap.range (Matrix.toLin' N)) :
    F M = F N := by
  obtain ⟨ U, V, hUV, hVU, hNU ⟩ := same_range_matrix_right_orbit M N h
  calc
    F M = F (N * U) := congrArg F hNU.symm
    _ = F N := hInv N U V hUV hVU

end
end PvNP.RealizableHardness.BinaryMatrixRightOrbit
