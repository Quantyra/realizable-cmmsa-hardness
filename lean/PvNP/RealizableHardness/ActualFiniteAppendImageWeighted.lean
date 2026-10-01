import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
import PvNP.RealizableHardness.GrassmannCounting

/-!
Per-image retained-frequency counting for the actual appended Fourier operator.
The fibre is fixed by the *same* image subspace throughout; no cross-image
coefficient constancy or full-rank sampling law is used.
-/
namespace PvNP.RealizableHardness.ActualFiniteAppendImageWeighted

open PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Rank-`i` matrices with fixed image `E` whose associated surjection
vanishes on the appended coordinate summand. -/
def RetainedMatrixImageFibre {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i) :=
  {A : MatrixImageFibre n (c + s) i E //
    (matrixImageFibreEquivSurjections E hE A).val.comp
      (appendRightInjection c s) = 0}

/-- The zero-appended part of a fixed-image matrix fibre is exactly the
surjection fibre on the base coordinates. This is a fibrewise equivalence,
not a statement after summing over image subspaces. -/
def retainedMatrixImageFibreEquiv {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i) :
    RetainedMatrixImageFibre E hE ≃ AppendedZeroSurjectionFibre c s E where
  toFun A :=
    ⟨(matrixImageFibreEquivSurjections E hE A.val).val,
      ⟨(matrixImageFibreEquivSurjections E hE A.val).property, A.property⟩⟩
  invFun f := by
    let g : SurjectionImageFibre (c + s) E := ⟨f.val, f.property.1⟩
    let A : MatrixImageFibre n (c + s) i E :=
      (matrixImageFibreEquivSurjections E hE).symm g
    have hA : matrixImageFibreEquivSurjections E hE A = g :=
      (matrixImageFibreEquivSurjections E hE).apply_symm_apply g
    exact ⟨A, by simpa [g, hA] using f.property.2⟩
  left_inv A := by
    apply Subtype.ext
    exact (matrixImageFibreEquivSurjections E hE).symm_apply_apply A.val
  right_inv f := by
    apply Subtype.ext
    exact congrArg Subtype.val
      ((matrixImageFibreEquivSurjections E hE).apply_symm_apply
        ⟨f.val, f.property.1⟩)

/-- Exact finite count of retained rank-`i`, image-`E` matrices. The proof
uses the matrix/surjection equivalence and the actual appended-zero
surjection equivalence; it does not postulate a fibre count. -/
theorem card_retainedMatrixImageFibre {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i) :
    Nat.card (RetainedMatrixImageFibre (c := c) (s := s) E hE) =
      frameProduct c i := by
  rw [Nat.card_congr (retainedMatrixImageFibreEquiv E hE)]
  simpa [hE] using card_appendedZeroSurjectionFibre (c := c) (s := s) E

/-- For any real statistic constant on a fixed image fibre, the retained
squared mass factors by the exact finite retained count. This is the local
weighted step used before summing over distinct `E`. -/
theorem retained_fibre_square_sum {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i)
    (a : MatrixImageFibre n (c + s) i E → Real)
    (v : Real) (ha : ∀ A, a A = v) :
    ∑ A : RetainedMatrixImageFibre (c := c) (s := s) E hE, (a A.val) ^ 2 =
      (Fintype.card (RetainedMatrixImageFibre (c := c) (s := s) E hE) : Real) * v ^ 2 := by
  have hconst : ∀ A : RetainedMatrixImageFibre (c := c) (s := s) E hE,
      a A.val = v := fun A => ha A.val
  simp_rw [hconst]
  simp

end
end PvNP.RealizableHardness.ActualFiniteAppendImageWeighted
