import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import PvNP.RealizableHardness.ActualBinaryMatrixHC46CommonA16

/-!
Finite-degree support and reconstruction for the actual complex rank
projections.  This is purely Fourier algebra on the full binary matrix space;
it assumes neither Booleanity nor a spectral/energy estimate.
-/
namespace PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.BinaryMatrixA1Complex
open PvNP.RealizableHardness.ActualBinaryMatrixHC46CommonA16
open PvNP.RealizableHardness.ActualBinaryMatrixHC46FourierA16

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact rank support for a complex function's Fourier coefficients. -/
def ComplexFourierSupportedThrough {n d : Nat} (D : Nat)
    (f : BinaryMatrix n d → Complex) : Prop :=
  ∀ Y, D < Y.rank → complexFourierCoeff f Y = 0

/-- Each complex rank projection has Fourier support on its selected rank. -/
theorem complexRankProjection_fourier_support {n d i : Nat}
    (f : BinaryMatrix n d → Complex) (Y : BinaryMatrix n d)
    (hY : Y.rank ≠ i) :
    complexFourierCoeff (complexRankProjection i f) Y = 0 := by
  apply Complex.ext
  · rw [BinaryMatrixA1Complex.complexFourierCoeff_re]
    simp_rw [complexRankProjection_re]
    exact rankProjection_fourier_support (fun X => (f X).re) Y hY
  · rw [BinaryMatrixA1Complex.complexFourierCoeff_im]
    simp_rw [complexRankProjection_im]
    exact rankProjection_fourier_support (fun X => (f X).im) Y hY

/-- A rank-`i` projection itself satisfies the degree support premise for
every cutoff `D ≥ i`. -/
theorem complexRankProjection_supportedThrough {n d i D : Nat}
    (hi : i ≤ D) (f : BinaryMatrix n d → Complex) :
    ComplexFourierSupportedThrough D (complexRankProjection i f) := by
  intro Y hY
  exact complexRankProjection_fourier_support f Y (by omega)

/-- A rank projection above the matrix column width has empty Fourier support. -/
theorem complexRankProjection_zero_of_width_lt {n d i : Nat}
    (hd : d < i) (f : BinaryMatrix n d → Complex) :
    complexRankProjection i f = 0 := by
  funext M
  unfold complexRankProjection
  apply Finset.sum_eq_zero
  intro Y hY
  have hrank : Y.rank = i := (Finset.mem_filter.mp hY).2
  have hwidth : Y.rank ≤ d := Matrix.rank_le_width Y
  omega

/-- Rank projections absent from the realized matrix-rank image vanish. -/
theorem complexRankProjection_zero_of_not_mem_rank_image {n d i : Nat}
    (hi : i ∉ (Finset.univ : Finset (BinaryMatrix n d)).image
      (fun Y => Y.rank)) (f : BinaryMatrix n d → Complex) :
    complexRankProjection i f = 0 := by
  funext M
  unfold complexRankProjection
  apply Finset.sum_eq_zero
  intro Y hY
  have hfilter : Y.rank = i := (Finset.mem_filter.mp hY).2
  apply False.elim
  apply hi
  exact Finset.mem_image.mpr ⟨Y, Finset.mem_univ Y, hfilter⟩

/-- A degree-support hypothesis kills every rank projection above its degree,
independently of the ambient number of columns. -/
theorem complexRankProjection_zero_of_level_gt {n d i D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f) (hdegree : D < i) :
    complexRankProjection i f = 0 := by
  funext M
  unfold complexRankProjection
  apply Finset.sum_eq_zero
  intro Y hY
  have hrank : Y.rank = i := (Finset.mem_filter.mp hY).2
  have hcoeff : complexFourierCoeff f Y = 0 := by
    apply hsupport
    omega
  simp [hcoeff]

/-- A function supported on Fourier ranks at most `D` reconstructs over the
literal finite range `0, …, D`, even when `D` is smaller than the ambient
column width. -/
theorem complexRankProjection_reconstruct_range_of_support {n d D : Nat}
    (f : BinaryMatrix n d → Complex)
    (hsupport : ComplexFourierSupportedThrough D f)
    (M : BinaryMatrix n d) :
    (∑ i ∈ Finset.range (D + 1), complexRankProjection i f M) = f M := by
  classical
  let ranks : Finset Nat :=
    (Finset.univ : Finset (BinaryMatrix n d)).image (fun Y => Y.rank)
  let lowRanks := ranks.filter (fun i => i ≤ D)
  have hlowRange : lowRanks ⊆ Finset.range (D + 1) := by
    intro i hi
    have hiD := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hiD)
  have hrangeZero : ∀ i ∈ Finset.range (D + 1), i ∉ lowRanks →
      complexRankProjection i f M = 0 := by
    intro i hi hnot
    have hiD : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hir : i ∈ ranks
    · have : i ∈ lowRanks := Finset.mem_filter.mpr ⟨hir, hiD⟩
      exact (hnot this).elim
    · have hir' : i ∉
          (Finset.univ : Finset (BinaryMatrix n d)).image (fun Y => Y.rank) := by
        simpa [ranks] using hir
      exact congrFun (complexRankProjection_zero_of_not_mem_rank_image hir' f) M
  have hlowRanks : lowRanks ⊆ ranks := Finset.filter_subset _ _
  have hrankZero : ∀ i ∈ ranks, i ∉ lowRanks →
      complexRankProjection i f M = 0 := by
    intro i hi hnot
    have hnotle : ¬ i ≤ D := by
      intro hle
      exact hnot (Finset.mem_filter.mpr ⟨hi, hle⟩)
    have hdegree : D < i := Nat.lt_of_not_ge hnotle
    exact congrFun (complexRankProjection_zero_of_level_gt f hsupport hdegree) M
  have hrangeLow :
      (∑ i ∈ Finset.range (D + 1), complexRankProjection i f M) =
        ∑ i ∈ lowRanks, complexRankProjection i f M := by
    symm
    exact Finset.sum_subset hlowRange hrangeZero
  have hlowImage :
      (∑ i ∈ lowRanks, complexRankProjection i f M) =
        ∑ i ∈ ranks, complexRankProjection i f M :=
    Finset.sum_subset hlowRanks hrankZero
  calc
    (∑ i ∈ Finset.range (D + 1), complexRankProjection i f M) =
        ∑ i ∈ lowRanks, complexRankProjection i f M := hrangeLow
    _ = ∑ i ∈ ranks, complexRankProjection i f M := hlowImage
    _ = f M := by
          dsimp [ranks]
          exact complexRankProjection_reconstruct f M

/-- Every actual complex function reconstructs using any finite rank window
that contains the column width.  The sum is over the literal range
`0, …, D`; ranks outside the realized image contribute zero. -/
theorem complexRankProjection_reconstruct_range {n d D : Nat}
    (hwidth : d ≤ D) (f : BinaryMatrix n d → Complex)
    (M : BinaryMatrix n d) :
    (∑ i ∈ Finset.range (D + 1), complexRankProjection i f M) = f M := by
  classical
  let ranks : Finset Nat :=
    (Finset.univ : Finset (BinaryMatrix n d)).image (fun Y => Y.rank)
  have hranks : ranks ⊆ Finset.range (D + 1) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨Y, -, rfl⟩
    apply Finset.mem_range.mpr
    have hY : Y.rank ≤ d := Matrix.rank_le_width Y
    omega
  have hzero : ∀ i ∈ Finset.range (D + 1), i ∉ ranks →
      complexRankProjection i f M = 0 := by
    intro i _ hi
    exact congrFun (complexRankProjection_zero_of_not_mem_rank_image hi f) M
  calc
    (∑ i ∈ Finset.range (D + 1), complexRankProjection i f M) =
        ∑ i ∈ ranks, complexRankProjection i f M := by
          rw [← Finset.sum_subset hranks hzero]
    _ = f M := by
          dsimp [ranks]
          exact complexRankProjection_reconstruct f M

end
end PvNP.RealizableHardness.ActualFiniteDegreeFourierReconstruction
