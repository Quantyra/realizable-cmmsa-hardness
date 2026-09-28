import PvNP.RealizableHardness.BinaryMatrixFourier

/-! Coordinate first domain-line derivative in Appendix A1/A14.
The selected frequency has one more rank than its induced frequency.
`BinaryMatrixHybridSelector` identifies this selector with the manuscript's
full-domain hybrid line selector. No A1/A14 theorem is asserted by this module. -/
namespace PvNP.RealizableHardness.BinaryMatrixFirstDerivative

open BinaryMatrixFourier
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def rawLastColumn {n d : ℕ} (M : BinaryMatrix n d)
    (t : Fin n → ZMod 2) : BinaryMatrix n (d + 1) :=
  fun i => Fin.snoc (M i) (t i)

def dropLastFrequency {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) : BinaryMatrix n d :=
  fun i j => Y i (Fin.castSucc j)

def lastFrequencyColumn {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) : Fin n → ZMod 2 :=
  fun i => Y i (Fin.last d)

theorem pairing_rawLastColumn {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (M : BinaryMatrix n d)
    (t : Fin n → ZMod 2) :
    pairing Y (rawLastColumn M t) =
      pairing (dropLastFrequency Y) M +
        ∑ i : Fin n, lastFrequencyColumn Y i * t i := by
  unfold pairing
  simp only [rawLastColumn, dropLastFrequency, lastFrequencyColumn]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_castSucc]
  simp

def lastColumnPhase {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (t : Fin n → ZMod 2) : ℝ :=
  if (∑ i : Fin n, lastFrequencyColumn Y i * t i) = 0 then 1 else -1

theorem character_rawLastColumn {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (M : BinaryMatrix n d)
    (t : Fin n → ZMod 2) :
    character Y (rawLastColumn M t) =
      lastColumnPhase Y t * character (dropLastFrequency Y) M := by
  rw [character, pairing_rawLastColumn]
  simp only [lastColumnPhase, character]
  rw [add_comm]
  exact BinaryMatrixFourier.bitSign_add _ _

/-- This is the actual rank selector for a domain-line derivative in these
coordinates, rather than an arbitrary rank predicate. -/
def selectedLastColumn {n d : ℕ} (Y : BinaryMatrix n (d + 1)) : Prop :=
  Y.rank = (dropLastFrequency Y).rank + 1

theorem selectedLastColumn_rank_shift {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (h : selectedLastColumn Y) :
    (dropLastFrequency Y).rank = Y.rank - 1 := by
  unfold selectedLastColumn at h
  omega

/-- A concrete Fourier-filtered raw restriction at one fixed domain line.
The filter is expressed by rank increase; `BinaryMatrixHybridSelector`
proves its equivalence with the full-domain hybrid line selector. -/
def lastColumnDerivative {n d : ℕ} (t : Fin n → ZMod 2)
    (f : BinaryMatrix n (d + 1) → ℝ) (M : BinaryMatrix n d) : ℝ :=
  ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (d + 1))).filter selectedLastColumn,
    fourierCoeff f Y * character Y (rawLastColumn M t)

theorem fourierCoeff_character {n d : ℕ}
    (Y Z : BinaryMatrix n d) :
    fourierCoeff (character Y) Z = if Z = Y then 1 else 0 := by
  simpa only [fourierCoeff, mul_comm, eq_comm] using
    character_orthogonality Y Z

/-- First actual derivative identity on a character: a selected input
frequency yields its induced lower-rank character with the exact base phase. -/
theorem lastColumnDerivative_character {n d : ℕ}
    (t : Fin n → ZMod 2) (Y : BinaryMatrix n (d + 1))
    (M : BinaryMatrix n d) :
    lastColumnDerivative t (character Y) M =
      if selectedLastColumn Y then
        lastColumnPhase Y t * character (dropLastFrequency Y) M
      else 0 := by
  unfold lastColumnDerivative
  simp_rw [fourierCoeff_character]
  by_cases h : selectedLastColumn Y
  · simp [h, character_rawLastColumn]
  · simp [h]

/-- At each rank `j`, the actual derivative keeps exactly selected original
frequencies of rank `j`; each term has induced rank `j-1`. This is the
frequencywise input to Appendix (A14)/(A22), before collision aggregation. -/
theorem lastColumnDerivative_rankProjection {n d j : ℕ}
    (t : Fin n → ZMod 2) (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n d) :
    lastColumnDerivative t (rankProjection j f) M =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (d + 1))).filter
          (fun Y => selectedLastColumn Y ∧ Y.rank = j),
        fourierCoeff f Y * lastColumnPhase Y t *
          character (dropLastFrequency Y) M := by
  unfold lastColumnDerivative
  simp_rw [fourierCoeff_rankProjection, character_rawLastColumn]
  simp only [Finset.sum_filter, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hs : selectedLastColumn Y <;>
    by_cases hr : Y.rank = j <;> simp [hs, hr, mul_assoc]

end
end PvNP.RealizableHardness.BinaryMatrixFirstDerivative
