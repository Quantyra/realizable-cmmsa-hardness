import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualFiniteAppendImageWeighted
import PvNP.RealizableHardness.ActualFiniteAppendSpectral47
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

/-!
Exact bridge between the retained fixed-image surjection predicate and the
zero appended Fourier block used by the actual unconditional append operator.
-/
namespace PvNP.RealizableHardness.ActualFiniteAppendImageTailBridge

open PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
open PvNP.RealizableHardness.ActualFiniteAppendImageWeighted
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.BinaryMatrixFourier

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Appending a zero block is exactly vanishing on the appended domain
summand. This is stated for the same unconditional matrix append map. -/
theorem appendMatrix_tail_comp_zero_iff {n c s : Nat}
    (Y : BinaryMatrix n c) (W : BinaryMatrix n s) :
    (appendBinaryMatrix Y W).mulVecLin.comp (appendRightInjection c s) = 0 ↔ W = 0 := by
  constructor
  · intro h
    ext i j
    have hpoint := congrFun (LinearMap.ext_iff.mp h
      (Pi.single j 1)) i
    simpa [appendBinaryMatrix, appendBinaryMatrixEquiv, appendCoordinateArrayEquiv,
      coordinateArrayBinaryMatrixEquiv, appendRightInjection, appendDomainEquiv,
      Matrix.mulVecLin_apply, Matrix.mulVec, Pi.single_apply] using hpoint
  · intro hW
    subst W
    ext x i
    simp [appendBinaryMatrix, appendBinaryMatrixEquiv, appendCoordinateArrayEquiv,
      coordinateArrayBinaryMatrixEquiv, appendRightInjection, appendDomainEquiv,
      Matrix.mulVecLin_apply, Matrix.mulVec]

/-- For a matrix `Z`, its appended Fourier block vanishes exactly when its
linear map kills the appended coordinate injection. -/
theorem appendedFrequencyPart_zero_iff_kills {n c s : Nat}
    (Z : BinaryMatrix n (c + s)) :
    appendedFrequencyPart Z = 0 ↔
      Z.mulVecLin.comp (appendRightInjection c s) = 0 := by
  let e := appendBinaryMatrixEquiv n c s
  let Y := (e.symm Z).1
  let W := (e.symm Z).2
  have hZ : appendBinaryMatrix Y W = Z := by
    change e (e.symm Z) = Z
    exact e.apply_symm_apply Z
  have hpart : appendedFrequencyPart (appendBinaryMatrix Y W) = W := by
    simp [appendedFrequencyPart, e, W]
  rw [← hZ, hpart]
  exact (appendMatrix_tail_comp_zero_iff Y W).symm

/-- The weighted module's retained predicate is the actual spectral surviving
predicate on every fixed image fibre. -/
theorem retained_iff_appendedFrequencyPart_zero {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i)
    (A : MatrixImageFibre n (c + s) i E) :
    (matrixImageFibreEquivSurjections E hE A).val.comp
        (appendRightInjection c s) = 0 ↔
      appendedFrequencyPart A.val = 0 := by
  have hrestrict :
      (matrixImageFibreEquivSurjections E hE A).val =
        A.val.mulVecLin.codRestrict E (fun x => by
          have hrange : LinearMap.range A.val.mulVecLin ≤ E := le_of_eq A.property.2
          exact hrange (LinearMap.mem_range_self _ x)) := by
    rfl
  rw [hrestrict]
  constructor
  · intro h
    apply appendedFrequencyPart_zero_iff_kills
    apply LinearMap.ext
    intro x
    have hx := LinearMap.ext_iff.mp h x
    have hx' := congrArg Subtype.val hx
    simpa [LinearMap.codRestrict_apply] using hx'
  · intro h
    have hk := (appendedFrequencyPart_zero_iff_kills A.val).mp h
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx := LinearMap.ext_iff.mp hk x
    simpa [LinearMap.codRestrict_apply] using hx

end
end PvNP.RealizableHardness.ActualFiniteAppendImageTailBridge
