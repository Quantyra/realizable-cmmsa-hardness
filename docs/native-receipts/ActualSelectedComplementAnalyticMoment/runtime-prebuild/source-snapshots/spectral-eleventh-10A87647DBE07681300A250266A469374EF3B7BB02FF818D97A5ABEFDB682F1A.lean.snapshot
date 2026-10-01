import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
import PvNP.RealizableHardness.ActualFiniteBinaryImageOrbit
import PvNP.RealizableHardness.ActualFiniteAppendSpectral47

/-!
Transport fixed-image surjection transitivity to the matrix right action and
apply the actual dual right-transpose Fourier invariance.  This proves
coefficient constancy within each individual image fibre; it makes no claim
that coefficients agree across distinct image subspaces.
-/

namespace PvNP.RealizableHardness.ActualFiniteBinaryImageOrbitFourier

open PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
open PvNP.RealizableHardness.ActualFiniteBinaryImageOrbit
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47
open PvNP.RealizableHardness.BinaryMatrixFourier

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Two rank-`i` matrices with the same image are in one right-`GL` orbit.
The matrix `U` is the action on domain columns, so the relation is `B * U = A`.
-/
theorem exists_right_action_same_image {n d i : Nat}
    {E : Submodule (ZMod 2) (Coord n)}
    (A B : MatrixImageFibre n d i E) :
    ∃ U V : BinaryMatrix d d,
      U * V = 1 ∧ V * U = 1 ∧ B.val * U = A.val := by
  have hE : Module.finrank (ZMod 2) E = i := by
    calc
      Module.finrank (ZMod 2) E =
          Module.finrank (ZMod 2) (LinearMap.range A.val.mulVecLin) := by
          exact congrArg
            (fun S : Submodule (ZMod 2) (Coord n) => Module.finrank (ZMod 2) S)
            A.property.2.symm
      _ = A.val.rank := rfl
      _ = i := A.property.1
  let f : SurjectionImageFibre d E := matrixImageFibreEquivSurjections E hE A
  let g : SurjectionImageFibre d E := matrixImageFibreEquivSurjections E hE B
  obtain ⟨Ue, hfg⟩ := exists_domain_equiv_of_surjective f.val g.val
    f.property g.property
  let U : BinaryMatrix d d := Matrix.toLin'.symm Ue.toLinearMap
  let V : BinaryMatrix d d := Matrix.toLin'.symm Ue.symm.toLinearMap
  have hU : U.mulVecLin = Ue.toLinearMap := by
    change Matrix.toLin' (Matrix.toLin'.symm Ue.toLinearMap) = _
    exact Matrix.toLin'.apply_symm_apply _
  have hV : V.mulVecLin = Ue.symm.toLinearMap := by
    change Matrix.toLin' (Matrix.toLin'.symm Ue.symm.toLinearMap) = _
    exact Matrix.toLin'.apply_symm_apply _
  have hUV : U * V = 1 := by
    apply Matrix.toLin'.injective
    change (U * V).mulVecLin = (1 : BinaryMatrix d d).mulVecLin
    rw [Matrix.mulVecLin_mul, hU, hV]
    ext x
    simp
  have hVU : V * U = 1 := by
    apply Matrix.toLin'.injective
    change (V * U).mulVecLin = (1 : BinaryMatrix d d).mulVecLin
    rw [Matrix.mulVecLin_mul, hV, hU]
    ext x
    simp
  have hfA : E.subtype.comp f.val = A.val.mulVecLin := by
    ext x
    rfl
  have hgB : E.subtype.comp g.val = B.val.mulVecLin := by
    ext x
    rfl
  have hBA : B.val.mulVecLin.comp Ue.toLinearMap = A.val.mulVecLin := by
    calc
      B.val.mulVecLin.comp Ue.toLinearMap =
          E.subtype.comp (g.val.comp Ue.toLinearMap) := by
            rw [← hgB]
            ext x
            rfl
      _ = E.subtype.comp f.val := by rw [hfg]
      _ = A.val.mulVecLin := hfA
  have hmul : (B.val * U).mulVecLin = A.val.mulVecLin := by
    rw [Matrix.mulVecLin_mul, hU]
    exact hBA
  have hmatrix : B.val * U = A.val := by
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_apply'] using hmul
  exact ⟨U, V, hUV, hVU, hmatrix⟩

/-- The rank-projection Fourier coefficient is constant on a fixed-image
matrix fibre, for every real base function invariant under two-sided basis
changes. -/
theorem fourierCoeff_rankProjection_eq_same_image {n d i : Nat}
    (F : BinaryMatrix n d → Real)
    (basisInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    {E : Submodule (ZMod 2) (Coord n)}
    (A B : MatrixImageFibre n d i E) :
    fourierCoeff (rankProjection i F) A.val =
      fourierCoeff (rankProjection i F) B.val := by
  obtain ⟨U, V, hUV, hVU, hBA⟩ := exists_right_action_same_image A B
  let W := U.transpose
  let Z := V.transpose
  have hWZ : W * Z = 1 := by
    dsimp [W, Z]
    calc
      U.transpose * V.transpose = (V * U).transpose := by
        rw [← Matrix.transpose_mul]
      _ = 1 := by rw [hVU, Matrix.transpose_one]
  have hZW : Z * W = 1 := by
    dsimp [W, Z]
    calc
      V.transpose * U.transpose = (U * V).transpose := by
        rw [← Matrix.transpose_mul]
      _ = 1 := by rw [hUV, Matrix.transpose_one]
  have hRankProjectionBasis : ∀ (M : BinaryMatrix n d) (X Y : BinaryMatrix d d),
      X * Y = 1 → Y * X = 1 →
      rankProjection i F (M * X) = rankProjection i F M := by
    intro M X Y hXY hYX
    exact rankProjection_mul_right_eq F basisInv M X Y hXY hYX
  have hcoeff := fourierCoeff_mul_right_transpose_eq
    (rankProjection i F) hRankProjectionBasis B.val W Z hWZ hZW
  simpa [W, hBA] using hcoeff

end
end PvNP.RealizableHardness.ActualFiniteBinaryImageOrbitFourier
