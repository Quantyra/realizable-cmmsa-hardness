import PvNP.RealizableHardness.BinaryMatrixHybridSelector

namespace PvNP.RealizableHardness.BinaryMatrixLineTranslation

open BinaryMatrixFourier BinaryMatrixFirstDerivative BinaryMatrixHybridSelector
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def lineFunctional {d : ℕ} (φ : Fin d → ZMod 2) : Fin (d + 1) → ZMod 2 :=
  Fin.snoc φ 1

def lineShift {n d : ℕ} (w : Fin n → ZMod 2)
    (φ : Fin d → ZMod 2) : BinaryMatrix n (d + 1) :=
  fun i j => w i * lineFunctional φ j

def lineFrequency {n d : ℕ} (Y : BinaryMatrix n (d + 1))
    (φ : Fin d → ZMod 2) : Fin n → ZMod 2 :=
  Y.mulVec (lineFunctional φ)

theorem pairing_lineShift {n d : ℕ} (Y : BinaryMatrix n (d + 1))
    (w : Fin n → ZMod 2) (φ : Fin d → ZMod 2) :
    pairing Y (lineShift w φ) =
      ∑ i : Fin n, lineFrequency Y φ i * w i := by
  unfold pairing lineShift lineFrequency Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private def columnEquiv (n : ℕ) :
    (Fin n → ZMod 2) ≃ BinaryMatrix n 1 where
  toFun w i _ := w i
  invFun A i := A i 0
  left_inv w := rfl
  right_inv A := by
    ext i j
    fin_cases j
    rfl

private def lineFrequencyMatrix {n d : ℕ} (Y : BinaryMatrix n (d + 1))
    (φ : Fin d → ZMod 2) : BinaryMatrix n 1 :=
  fun i _ => lineFrequency Y φ i

private theorem character_lineShift_column {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (φ : Fin d → ZMod 2)
    (w : Fin n → ZMod 2) :
    character Y (lineShift w φ) =
      character (lineFrequencyMatrix Y φ) (columnEquiv n w) := by
  unfold character
  rw [pairing_lineShift]
  congr 1
  simp [pairing, lineFrequencyMatrix, columnEquiv]
  rfl

theorem lineShift_character_sum {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (φ : Fin d → ZMod 2) :
    (∑ w : Fin n → ZMod 2, character Y (lineShift w φ)) =
      if lineFrequency Y φ = 0 then
        (Fintype.card (Fin n → ZMod 2) : ℝ) else 0 := by
  let Z := lineFrequencyMatrix Y φ
  have hs : (∑ w : Fin n → ZMod 2, character Y (lineShift w φ)) =
      ∑ A : BinaryMatrix n 1, character Z A := by
    exact Fintype.sum_equiv (columnEquiv n) _ _ (character_lineShift_column Y φ)
  rw [hs]
  by_cases hz : lineFrequency Y φ = 0
  · have hZ : Z = 0 := by
      ext i j
      simp [Z, lineFrequencyMatrix, hz]
    have hcard : Fintype.card (BinaryMatrix n 1) =
        Fintype.card (Fin n → ZMod 2) :=
      Fintype.card_congr (columnEquiv n).symm
    simp [hz, hZ, character, pairing, hcard]
  · have hZ : Z ≠ 0 := by
      intro h
      apply hz
      funext i
      have hi := congrArg (fun A : BinaryMatrix n 1 => A i 0) h
      simpa [Z, lineFrequencyMatrix] using hi
    simpa [hz] using character_sum_zero_of_ne Z hZ

theorem lineFrequency_ne_zero_of_hybridLineSelected {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (hY : hybridLineSelected Y)
    (φ : Fin d → ZMod 2) : lineFrequency Y φ ≠ 0 := by
  intro hzero
  obtain ⟨w, hw⟩ := hY
  have hpair := Matrix.dotProduct_transpose_mulVec Y (lineFunctional φ) w
  have hw' : Y.transpose.mulVec w = Pi.single (Fin.last d) (1 : ZMod 2) := hw
  rw [hw'] at hpair
  have hl : (lineFunctional φ) (Fin.last d) = 1 := by
    simp [lineFunctional]
  have hleft : lineFunctional φ ⬝ᵥ (Pi.single (Fin.last d) (1 : ZMod 2)) = 1 := by
    simp [dotProduct, Pi.single_apply, hl]
  have hright : w ⬝ᵥ Y.mulVec (lineFunctional φ) = 0 := by
    simp [lineFrequency] at hzero
    rw [hzero]
    simp
  exact one_ne_zero (hleft.symm.trans (hpair.trans hright))

def lineTranslationAverage {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) : ℝ :=
  (∑ φ : Fin d → ZMod 2, ∑ w : Fin n → ZMod 2,
      f (M + lineShift w φ)) /
    ((Fintype.card (Fin d → ZMod 2) : ℝ) *
      (Fintype.card (Fin n → ZMod 2) : ℝ))

def lineTranslationMultiplier {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) : ℝ :=
  (∑ φ : Fin d → ZMod 2, ∑ w : Fin n → ZMod 2,
      character Y (lineShift w φ)) /
    ((Fintype.card (Fin d → ZMod 2) : ℝ) *
      (Fintype.card (Fin n → ZMod 2) : ℝ))

def affineKernelFraction {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) : ℝ :=
  (∑ φ : Fin d → ZMod 2,
      if lineFrequency Y φ = 0 then (1 : ℝ) else 0) /
    (Fintype.card (Fin d → ZMod 2) : ℝ)

/-- Averaging the independent row shift leaves exactly the fraction of
line functionals in the kernel of `Y`. This is the finite count required
to evaluate the manuscript multiplier in A13. -/
theorem lineTranslationMultiplier_eq_affineKernelFraction {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) :
    lineTranslationMultiplier Y = affineKernelFraction Y := by
  unfold lineTranslationMultiplier affineKernelFraction
  simp_rw [lineShift_character_sum]
  have hw : (Fintype.card (Fin n → ZMod 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin n → ZMod 2)).ne'
  have hs :
      (∑ φ : Fin d → ZMod 2,
        if lineFrequency Y φ = 0 then
          (Fintype.card (Fin n → ZMod 2) : ℝ) else 0) =
      (∑ φ : Fin d → ZMod 2,
        if lineFrequency Y φ = 0 then (1 : ℝ) else 0) *
          (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro φ _
    split <;> simp
  rw [hs]
  field_simp

theorem affineKernelFraction_eq_zero_of_hybridLineSelected {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (hY : hybridLineSelected Y) :
    affineKernelFraction Y = 0 := by
  unfold affineKernelFraction
  simp [lineFrequency_ne_zero_of_hybridLineSelected Y hY]

theorem lineTranslationMultiplier_eq_zero_of_hybridLineSelected {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (hY : hybridLineSelected Y) :
    lineTranslationMultiplier Y = 0 := by
  rw [lineTranslationMultiplier_eq_affineKernelFraction]
  exact affineKernelFraction_eq_zero_of_hybridLineSelected Y hY

/-- The manuscript polynomial `P_{j+1}=(I-2^{j+1}E)(I-2^j E)`.
The successor index makes the stated `j ≥ 1` boundary explicit. -/
def lineIminusE {n d : ℕ} (a : ℝ)
    (f : BinaryMatrix n (d + 1) → ℝ) :
    BinaryMatrix n (d + 1) → ℝ :=
  fun M => f M - a * lineTranslationAverage f M

def lineP (j : ℕ) {n d : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ) :
    BinaryMatrix n (d + 1) → ℝ :=
  lineIminusE ((2 : ℝ) ^ (j + 1)) (lineIminusE ((2 : ℝ) ^ j) f)

/-- The actual translation operator is diagonal on the binary characters.
Its multiplier is the finite affine-kernel count in the definition above. -/
theorem lineTranslationAverage_character {n d : ℕ}
    (Y M : BinaryMatrix n (d + 1)) :
    lineTranslationAverage (character Y) M =
      lineTranslationMultiplier Y * character Y M := by
  unfold lineTranslationAverage lineTranslationMultiplier
  simp_rw [character_add_right]
  have hsum :
      (∑ φ : Fin d → ZMod 2, ∑ w : Fin n → ZMod 2,
        character Y M * character Y (lineShift w φ)) =
      character Y M *
        (∑ φ : Fin d → ZMod 2, ∑ w : Fin n → ZMod 2,
          character Y (lineShift w φ)) := by
    simp_rw [Finset.mul_sum]
  rw [hsum]
  ring

end
end PvNP.RealizableHardness.BinaryMatrixLineTranslation
