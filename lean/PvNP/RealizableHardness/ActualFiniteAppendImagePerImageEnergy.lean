import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualFiniteAppendImageWeighted
import PvNP.RealizableHardness.ActualFiniteFrameProductRatio
import PvNP.RealizableHardness.ActualFiniteBinaryImageOrbitFourier
import PvNP.RealizableHardness.BinaryMatrixFourier

/-! Fixed-image weighted Fourier energy from basis-orbit constancy. -/
namespace PvNP.RealizableHardness.ActualFiniteAppendImagePerImageEnergy

open PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
open PvNP.RealizableHardness.ActualFiniteAppendImageWeighted
open PvNP.RealizableHardness.ActualFiniteBinaryImageOrbitFourier
open PvNP.RealizableHardness.ActualFiniteFrameProductRatio
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.GrassmannCounting

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

instance matrixImageFibreFinite {n d i : Nat}
    (E : Submodule (ZMod 2) (Coord n)) :
    Finite (MatrixImageFibre n d i E) :=
  Finite.of_injective (fun A : MatrixImageFibre n d i E => A.val)
    (by intro A B h; exact Subtype.ext h)

noncomputable instance matrixImageFibreFintype {n d i : Nat}
    (E : Submodule (ZMod 2) (Coord n)) :
    Fintype (MatrixImageFibre n d i E) := Fintype.ofFinite _

/-- Within a fixed image `E`, the retained squared Fourier mass is exactly
its finite retained count times the squared coefficient at any chosen
representative. The constancy proof is the actual all-matrix GL invariance
route, applied only inside this one image fibre. -/
theorem retained_fourier_square_sum {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i)
    (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
        U * V = 1 → V * U = 1 → F (M * U) = F M)
    (A₀ : MatrixImageFibre n (c + s) i E) :
    ∑ A : RetainedMatrixImageFibre (c := c) (s := s) E hE,
        (fourierCoeff (rankProjection i F) A.val.val) ^ 2 =
      (Fintype.card (RetainedMatrixImageFibre (c := c) (s := s) E hE) : Real) *
        (fourierCoeff (rankProjection i F) A₀.val) ^ 2 := by
  apply retained_fibre_square_sum E hE
    (fun A => fourierCoeff (rankProjection i F) A.val)
    (fourierCoeff (rankProjection i F) A₀.val)
  intro A
  exact fourierCoeff_rankProjection_eq_same_image F basisInv A A₀

/-- The unretained coefficient-square sum on a fixed image fibre also
factors by its exact matrix count. -/
theorem image_fibre_fourier_square_sum {n d i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i)
    (F : BinaryMatrix n d → Real)
    (basisInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
        U * V = 1 → V * U = 1 → F (M * U) = F M)
    (A₀ : MatrixImageFibre n d i E) :
    ∑ A : MatrixImageFibre n d i E,
        (fourierCoeff (rankProjection i F) A.val) ^ 2 =
      (Fintype.card (MatrixImageFibre n d i E) : Real) *
        (fourierCoeff (rankProjection i F) A₀.val) ^ 2 := by
  have hconst : ∀ A : MatrixImageFibre n d i E,
      fourierCoeff (rankProjection i F) A.val =
        fourierCoeff (rankProjection i F) A₀.val := by
    intro A
    exact fourierCoeff_rankProjection_eq_same_image F basisInv A A₀
  simp_rw [hconst]
  simp

private theorem frameProduct_pos_of_le {d i : Nat} (hi : i ≤ d) :
    0 < frameProduct d i := by
  apply Finset.prod_pos
  intro j hj
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

/-- Exact fixed-image survivor-energy ratio. This is the weighted step before
summing distinct image subspaces: its only constancy input is the proved
right-GL invariance inside this same `E`. -/
theorem per_image_fourier_energy_ratio {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i)
    (hi : i ≤ c + s)
    (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
        U * V = 1 → V * U = 1 → F (M * U) = F M)
    (A₀ : MatrixImageFibre n (c + s) i E) :
    ∑ A : RetainedMatrixImageFibre (c := c) (s := s) E hE,
        (fourierCoeff (rankProjection i F) A.val.val) ^ 2 ≤
      (2 : Real) ^ (-((i : Real) * (s : Real))) *
        ∑ A : MatrixImageFibre n (c + s) i E,
          (fourierCoeff (rankProjection i F) A.val) ^ 2 := by
  have hret := retained_fourier_square_sum E hE F basisInv A₀
  have hall := image_fibre_fourier_square_sum E hE F basisInv A₀
  have hretCount :
      (Fintype.card (RetainedMatrixImageFibre (c := c) (s := s) E hE) : Real) =
        (frameProduct c i : Real) := by
    calc
      _ = (Nat.card (RetainedMatrixImageFibre (c := c) (s := s) E hE) : Real) := by
        rw [Nat.card_eq_fintype_card]
      _ = _ := by rw [card_retainedMatrixImageFibre E hE]
  have hallCount :
      (Fintype.card (MatrixImageFibre n (c + s) i E) : Real) =
        (frameProduct (c + s) i : Real) := by
    calc
      _ = (Nat.card (MatrixImageFibre n (c + s) i E) : Real) := by
        rw [Nat.card_eq_fintype_card]
      _ = _ := by rw [card_matrixImageFibre E hE]
  have hden : 0 < (frameProduct (c + s) i : Real) := by
    exact_mod_cast frameProduct_pos_of_le hi
  have hcounts : (frameProduct c i : Real) ≤
      (2 : Real) ^ (-((i : Real) * (s : Real))) *
        (frameProduct (c + s) i : Real) :=
    (div_le_iff₀ hden).mp frameProduct_ratio_le
  rw [hret, hall, hretCount, hallCount]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right hcounts (sq_nonneg _)

end
end PvNP.RealizableHardness.ActualFiniteAppendImagePerImageEnergy
