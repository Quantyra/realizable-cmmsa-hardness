import PvNP.RealizableHardness.ActualFiniteAppendGlobalImageEnergy
import PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant

/-! Exact energy identity for the actual unconditional append operator.
This candidate advances the reviewed fixed-image ratio argument. It does not
yet identify the quotient with the manuscript's s-factor eigenvalue formula
or prove the G/Phi operator laws. Native verification remains required. -/
namespace PvNP.RealizableHardness.ActualFiniteAppendExactImageEnergy

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFiniteBinaryImageFibres
open PvNP.RealizableHardness.ActualFiniteAppendImageWeighted
open PvNP.RealizableHardness.ActualFiniteAppendImagePerImageEnergy
open PvNP.RealizableHardness.ActualFiniteAppendGlobalImageEnergy
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47
open PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem frameProduct_pos {d i : Nat} (hi : i ≤ d) :
    0 < frameProduct d i := by
  apply Finset.prod_pos
  intro j hj
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)

private theorem rank_subtype_sum {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (g : α → Real) :
    (∑ x : {x // p x}, g x.1) = ∑ x ∈ Finset.univ.filter p, g x := by
  classical
  simpa only [Finset.subtype_univ] using
    (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α)) (p := p) g).symm

/-- Exact equality on a single image fibre, with empty fibres handled explicitly. -/
theorem per_image_energy_eq {n c s i : Nat}
    (E : Submodule (ZMod 2) (Coord n))
    (hE : Module.finrank (ZMod 2) E = i) (hi : i ≤ c + s)
    (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    (∑ A : RetainedMatrixImageFibre (c := c) (s := s) E hE,
      (fourierCoeff (rankProjection i F) A.1.1) ^ 2) =
    ((frameProduct c i : Real) / (frameProduct (c + s) i : Real)) *
      ∑ A : MatrixImageFibre n (c + s) i E,
        (fourierCoeff (rankProjection i F) A.1) ^ 2 := by
  classical
  by_cases hEmpty : IsEmpty (MatrixImageFibre n (c + s) i E)
  · letI := hEmpty
    letI : IsEmpty (RetainedMatrixImageFibre (c := c) (s := s) E hE) :=
      ⟨fun A => hEmpty.false A.1⟩
    simp
  · have hne : Nonempty (MatrixImageFibre n (c + s) i E) := by
      by_contra hn
      exact hEmpty ⟨fun A => hn ⟨A⟩⟩
    let A₀ := Classical.choice hne
    rw [retained_fourier_square_sum E hE F basisInv A₀,
      image_fibre_fourier_square_sum E hE F basisInv A₀]
    have hret : Fintype.card (RetainedMatrixImageFibre (c := c) (s := s) E hE) =
        frameProduct c i := by
      rw [← Nat.card_eq_fintype_card, card_retainedMatrixImageFibre E hE]
    have hall : Fintype.card (MatrixImageFibre n (c + s) i E) =
        frameProduct (c + s) i := by
      rw [← Nat.card_eq_fintype_card, card_matrixImageFibre E hE]
    rw [hret, hall]
    have hden : (frameProduct (c + s) i : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (frameProduct_pos hi))
    field_simp [hden] <;> ring

/-- Partition by the actual image; the quotient is the same for every image. -/
theorem rank_i_retained_energy_eq {n c s i : Nat}
    (hi : i ≤ c + s) (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    (∑ Z : RankMatrixType n (c + s) i,
      if appendedFrequencyPart Z.1 = 0 then
        (fourierCoeff (rankProjection i F) Z.1) ^ 2 else 0) =
    ((frameProduct c i : Real) / (frameProduct (c + s) i : Real)) *
      ∑ Z : RankMatrixType n (c + s) i,
        (fourierCoeff (rankProjection i F) Z.1) ^ 2 := by
  rw [sum_retained_matrices_by_image
      (g := fun Z => (fourierCoeff (rankProjection i F) Z) ^ 2),
    sum_rank_matrices_by_image
      (g := fun Z => (fourierCoeff (rankProjection i F) Z) ^ 2), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  exact per_image_energy_eq E.1 E.2 hi F basisInv

/-- Exact projected-energy equality for the original unconditional append. -/
theorem append_rank_projection_energy_eq_frame_ratio {n c s i : Nat}
    (hi : i ≤ c + s) (F : BinaryMatrix n (c + s) → Real)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    uniformMean (fun M : BinaryMatrix n c =>
      (appendAverage (rankProjection i F) M) ^ 2) =
    ((frameProduct c i : Real) / (frameProduct (c + s) i : Real)) *
      uniformMean (fun W : BinaryMatrix n (c + s) => (rankProjection i F W) ^ 2) := by
  classical
  have hglobal := rank_i_retained_energy_eq hi F basisInv
  have hcoeff (Z : RankMatrixType n (c + s) i) :
      fourierCoeff (rankProjection i F) Z.1 = fourierCoeff F Z.1 := by
    rw [fourierCoeff_rankProjection]
    simp [Z.2]
  simp_rw [hcoeff] at hglobal
  rw [appendAverage_rankProjection_energy_eq]
  have hleft := rank_subtype_sum (fun Z : BinaryMatrix n (c + s) => Z.rank = i)
    (fun Z => if appendedFrequencyPart Z = 0 then (fourierCoeff F Z) ^ 2 else 0)
  have hright := rank_subtype_sum (fun Z : BinaryMatrix n (c + s) => Z.rank = i)
    (fun Z => (fourierCoeff F Z) ^ 2)
  rw [← hleft, ← rankProjection_parseval_restricted_eq (i := i) F, ← hright]
  exact hglobal

end
end PvNP.RealizableHardness.ActualFiniteAppendExactImageEnergy
