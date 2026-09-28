import PvNP.RealizableHardness.BinaryMatrixHybridSelector
import Mathlib.FieldTheory.Finiteness

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

private def zeroLast {d : ℕ} (φ : Fin d → ZMod 2) :
    Fin (d + 1) → ZMod 2 := Fin.snoc φ 0

private theorem lineFunctional_eq_zeroLast_add_basis {d : ℕ}
    (φ : Fin d → ZMod 2) :
    lineFunctional φ = zeroLast φ + Pi.single (Fin.last d) (1 : ZMod 2) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [lineFunctional, zeroLast]
  | cast j => simp [lineFunctional, zeroLast]

private theorem full_mulVec_zeroLast {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (φ : Fin d → ZMod 2) :
    Y.mulVec (zeroLast φ) = (dropLastFrequency Y).mulVec φ := by
  funext i
  simp [Matrix.mulVec, dotProduct, zeroLast, dropLastFrequency,
    Fin.sum_univ_castSucc]

private theorem full_mulVec_lastBasis {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) :
    Y.mulVec (Pi.single (Fin.last d) (1 : ZMod 2)) =
      lastFrequencyColumn Y := by
  funext i
  simp [Matrix.mulVec, dotProduct, lastFrequencyColumn, Pi.single_apply]

private theorem lineFrequency_eq_drop_add_last {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (φ : Fin d → ZMod 2) :
    lineFrequency Y φ =
      (dropLastFrequency Y).mulVec φ + lastFrequencyColumn Y := by
  unfold lineFrequency
  rw [lineFunctional_eq_zeroLast_add_basis, Matrix.mulVec_add,
    full_mulVec_zeroLast, full_mulVec_lastBasis]

theorem exists_lineFrequency_zero_of_not_hybridLineSelected {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) (hY : ¬ hybridLineSelected Y) :
    ∃ φ : Fin d → ZMod 2, lineFrequency Y φ = 0 := by
  let A := (dropLastFrequency Y).mulVecLin
  let B := Y.mulVecLin
  have hle : LinearMap.range A ≤ LinearMap.range B := by
    rintro v ⟨φ, rfl⟩
    exact ⟨zeroLast φ, by simpa [A, B] using
      full_mulVec_zeroLast Y φ⟩
  have hrank : Y.rank = (dropLastFrequency Y).rank := by
    rw [rank_eq_drop_add_hybrid_indicator]
    simp [hybridLineSelected] at hY
    simp [hY]
  have heq : LinearMap.range A = LinearMap.range B := by
    apply Submodule.eq_of_le_of_finrank_le hle
    change (dropLastFrequency Y).rank ≥ Y.rank
    omega
  have hb : lastFrequencyColumn Y ∈ LinearMap.range B := by
    exact ⟨Pi.single (Fin.last d) (1 : ZMod 2),
      by simpa [B] using full_mulVec_lastBasis Y⟩
  rw [← heq] at hb
  obtain ⟨φ, hφ⟩ := hb
  refine ⟨φ, ?_⟩
  rw [lineFrequency_eq_drop_add_last]
  have hφ' : (dropLastFrequency Y).mulVec φ = lastFrequencyColumn Y := hφ
  rw [hφ']
  funext i
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    lastFrequencyColumn Y i + lastFrequencyColumn Y i =
        (2 : ZMod 2) * lastFrequencyColumn Y i := (two_mul _).symm
    _ = 0 := by simp [htwo]

private theorem affineKernel_card_eq_ker {n d : ℕ}
    (Y : BinaryMatrix n (d + 1))
    (φ₀ : Fin d → ZMod 2) (hφ₀ : lineFrequency Y φ₀ = 0) :
    Fintype.card {φ : Fin d → ZMod 2 // lineFrequency Y φ = 0} =
      Fintype.card (LinearMap.ker (dropLastFrequency Y).mulVecLin) := by
  let A := (dropLastFrequency Y).mulVecLin
  have hline (φ : Fin d → ZMod 2) :
      lineFrequency Y φ = 0 ↔ A φ = A φ₀ := by
    have h0 := hφ₀
    rw [lineFrequency_eq_drop_add_last] at h0
    rw [lineFrequency_eq_drop_add_last]
    constructor
    · intro h
      apply add_right_cancel (b := lastFrequencyColumn Y)
      exact h.trans h0.symm
    · intro h
      change (dropLastFrequency Y).mulVec φ =
        (dropLastFrequency Y).mulVec φ₀ at h
      rw [h]
      exact h0
  let e : {φ : Fin d → ZMod 2 // lineFrequency Y φ = 0} ≃
      LinearMap.ker A := {
    toFun x := ⟨x.val - φ₀, by
      change A (x.val - φ₀) = 0
      rw [map_sub, (hline x.val).mp x.property, sub_self]⟩
    invFun k := ⟨k.val + φ₀, by
      apply (hline _).mpr
      rw [map_add, show A k.val = 0 from k.property, zero_add]⟩
    left_inv x := by
      apply Subtype.ext
      simp
    right_inv k := by
      apply Subtype.ext
      simp
  }
  exact Fintype.card_congr e

def affineKernelFraction {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) : ℝ :=
  (∑ φ : Fin d → ZMod 2,
      if lineFrequency Y φ = 0 then (1 : ℝ) else 0) /
    (Fintype.card (Fin d → ZMod 2) : ℝ)

theorem affineKernelFraction_eq_invTwo_pow_rank_of_not_hybridLineSelected
    {n d : ℕ} (Y : BinaryMatrix n (d + 1))
    (hY : ¬ hybridLineSelected Y) :
    affineKernelFraction Y = ((2 : ℝ)⁻¹) ^ Y.rank := by
  obtain ⟨φ₀, hφ₀⟩ := exists_lineFrequency_zero_of_not_hybridLineSelected Y hY
  let A := (dropLastFrequency Y).mulVecLin
  have hrank : Y.rank = (dropLastFrequency Y).rank := by
    rw [rank_eq_drop_add_hybrid_indicator]
    simp [hybridLineSelected] at hY
    simp [hY]
  have hdim := A.finrank_range_add_finrank_ker
  have hdomain : Module.finrank (ZMod 2) (Fin d → ZMod 2) = d := by simp
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker A) = d - Y.rank := by
    have hdim' : (dropLastFrequency Y).rank +
        Module.finrank (ZMod 2) ↥(LinearMap.ker A) = d := by
      simpa [A, Matrix.rank, hdomain] using hdim
    omega
  have hle : Y.rank ≤ d := by
    have hdim' : (dropLastFrequency Y).rank +
        Module.finrank (ZMod 2) ↥(LinearMap.ker A) = d := by
      simpa [A, Matrix.rank, hdomain] using hdim
    omega
  have hcard : Fintype.card {φ : Fin d → ZMod 2 // lineFrequency Y φ = 0} =
      2 ^ (d - Y.rank) := by
    rw [affineKernel_card_eq_ker Y φ₀ hφ₀,
      Module.card_eq_pow_finrank (K := ZMod 2), hker]
    simp
  have hsum : (∑ φ : Fin d → ZMod 2,
      if lineFrequency Y φ = 0 then (1 : ℝ) else 0) =
      (Fintype.card {φ : Fin d → ZMod 2 // lineFrequency Y φ = 0} : ℝ) := by
    simpa [Fintype.card_subtype] using
      (Finset.sum_boole (p := fun φ : Fin d → ZMod 2 => lineFrequency Y φ = 0)
        (s := Finset.univ) (R := ℝ))
  have hden : Fintype.card (Fin d → ZMod 2) = 2 ^ d := by simp
  unfold affineKernelFraction
  rw [hsum, hcard, hden]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - Y.rank) * (2 : ℝ) ^ Y.rank := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, inv_pow]
  have hne : (2 : ℝ) ^ (d - Y.rank) ≠ 0 := by positivity
  field_simp

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

/-- The exact order-one translation multiplier from manuscript (A13),
including both selected and unselected frequencies. -/
theorem lineTranslationMultiplier_eq_hybrid {n d : ℕ}
    (Y : BinaryMatrix n (d + 1)) :
    lineTranslationMultiplier Y =
      if hybridLineSelected Y then 0 else ((2 : ℝ)⁻¹) ^ Y.rank := by
  by_cases hY : hybridLineSelected Y
  · simp [hY, lineTranslationMultiplier_eq_zero_of_hybridLineSelected Y hY]
  · rw [if_neg hY, lineTranslationMultiplier_eq_affineKernelFraction]
    exact affineKernelFraction_eq_invTwo_pow_rank_of_not_hybridLineSelected Y hY

/-- The manuscript polynomial `P_{j+1}=(I-2^{j+1}E)(I-2^j E)`.
The input index is any natural number; manuscript uses `P_k` at `k≥1`. -/
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

theorem lineTranslationAverage_character_explicit {n d : ℕ}
    (Y M : BinaryMatrix n (d + 1)) :
    lineTranslationAverage (character Y) M =
      (if hybridLineSelected Y then 0 else ((2 : ℝ)⁻¹) ^ Y.rank) *
        character Y M := by
  rw [lineTranslationAverage_character, lineTranslationMultiplier_eq_hybrid]

theorem lineTranslationAverage_add {n d : ℕ}
    (f g : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineTranslationAverage (fun N => f N + g N) M =
      lineTranslationAverage f M + lineTranslationAverage g M := by
  unfold lineTranslationAverage
  simp only [Finset.sum_add_distrib]
  ring

theorem lineTranslationAverage_mul {n d : ℕ}
    (a : ℝ) (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineTranslationAverage (fun N => a * f N) M =
      a * lineTranslationAverage f M := by
  unfold lineTranslationAverage
  simp only [← Finset.mul_sum]
  ring

theorem lineTranslationAverage_finset_sum {n d : ℕ}
    {α : Type*} (s : Finset α)
    (g : α → BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineTranslationAverage (fun N => ∑ a ∈ s, g a N) M =
      ∑ a ∈ s, lineTranslationAverage (g a) M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lineTranslationAverage]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [lineTranslationAverage_add, ih]

theorem lineTranslationAverage_rankProjection {n d j : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineTranslationAverage (rankProjection j f) M =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (d + 1))).filter
          (fun Y => Y.rank = j),
        fourierCoeff f Y * lineTranslationMultiplier Y * character Y M := by
  unfold rankProjection
  rw [lineTranslationAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [lineTranslationAverage_mul, lineTranslationAverage_character]
  ring

private theorem lineFilter_scalar_at_rank {n d j : ℕ}
    (Y : BinaryMatrix n (d + 1)) (hY : Y.rank = j) :
    (if hybridLineSelected Y then (1 : ℝ) else 0) =
      1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y := by
  rw [lineTranslationMultiplier_eq_hybrid]
  by_cases hs : hybridLineSelected Y
  · simp [hs]
  · simp only [if_neg hs, hY]
    have hp : (2 : ℝ) ^ j * ((2 : ℝ)⁻¹) ^ j = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hp]
    ring

/-- Function-level Appendix (A13) for the actual final-line translation
average. It holds also at rank zero; the manuscript uses it at `j ≥ 1`. -/
theorem hybridLineFilter_rankProjection_eq_sub_translation {n d j : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    hybridLineFilter (rankProjection j f) M =
      rankProjection j f M -
        (2 : ℝ) ^ j * lineTranslationAverage (rankProjection j f) M := by
  let s : Finset (BinaryMatrix n (d + 1)) :=
    Finset.univ.filter (fun Y => Y.rank = j)
  have hL : hybridLineFilter (rankProjection j f) M =
      ∑ Y ∈ s, (if hybridLineSelected Y then
        fourierCoeff f Y * character Y M else 0) := by
    unfold hybridLineFilter
    simp_rw [fourierCoeff_rankProjection]
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hs : hybridLineSelected Y <;>
      by_cases hr : Y.rank = j <;> simp [s, hs, hr]
  rw [hL, lineTranslationAverage_rankProjection]
  unfold rankProjection
  change (∑ Y ∈ s, if hybridLineSelected Y then
      fourierCoeff f Y * character Y M else 0) =
    (∑ Y ∈ s, fourierCoeff f Y * character Y M) -
      (2 : ℝ) ^ j *
        (∑ Y ∈ s, fourierCoeff f Y * lineTranslationMultiplier Y * character Y M)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro Y hYs
  have hY : Y.rank = j := (Finset.mem_filter.mp hYs).2
  have hs := lineFilter_scalar_at_rank Y hY
  split_ifs with hsel
  · simp [hsel] at hs
    rw [lineTranslationMultiplier_eq_zero_of_hybridLineSelected Y hsel]
    ring
  · simp [hsel] at hs
    calc
      (0 : ℝ) =
        (1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y) *
          (fourierCoeff f Y * character Y M) := by rw [← hs]; ring
      _ = fourierCoeff f Y * character Y M -
            (2 : ℝ) ^ j *
              (fourierCoeff f Y * lineTranslationMultiplier Y * character Y M) := by ring

private theorem lineIminusE_add {n d : ℕ} (a : ℝ)
    (f g : BinaryMatrix n (d + 1) → ℝ) (M : BinaryMatrix n (d + 1)) :
    lineIminusE a (fun N => f N + g N) M =
      lineIminusE a f M + lineIminusE a g M := by
  unfold lineIminusE
  rw [lineTranslationAverage_add]
  ring

private theorem lineIminusE_mul {n d : ℕ} (a b : ℝ)
    (f : BinaryMatrix n (d + 1) → ℝ) (M : BinaryMatrix n (d + 1)) :
    lineIminusE a (fun N => b * f N) M = b * lineIminusE a f M := by
  unfold lineIminusE
  rw [lineTranslationAverage_mul]
  ring

private theorem lineIminusE_finset_sum {n d : ℕ} (a : ℝ)
    {α : Type*} (s : Finset α)
    (g : α → BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineIminusE a (fun N => ∑ x ∈ s, g x N) M =
      ∑ x ∈ s, lineIminusE a (g x) M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lineIminusE, lineTranslationAverage]
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      rw [lineIminusE_add, ih]

private theorem lineP_finset_sum {n d j : ℕ}
    {α : Type*} (s : Finset α)
    (g : α → BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineP j (fun N => ∑ x ∈ s, g x N) M =
      ∑ x ∈ s, lineP j (g x) M := by
  unfold lineP
  have hinner : lineIminusE ((2 : ℝ) ^ j) (fun N => ∑ x ∈ s, g x N) =
      fun N => ∑ x ∈ s, lineIminusE ((2 : ℝ) ^ j) (g x) N := by
    funext N
    exact lineIminusE_finset_sum _ s g N
  rw [hinner]
  exact lineIminusE_finset_sum _ s _ M

private theorem lineP_mul {n d j : ℕ}
    (b : ℝ) (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineP j (fun N => b * f N) M = b * lineP j f M := by
  unfold lineP
  have hinner : lineIminusE ((2 : ℝ) ^ j) (fun N => b * f N) =
      fun N => b * lineIminusE ((2 : ℝ) ^ j) f N := by
    funext N
    exact lineIminusE_mul _ b f N
  rw [hinner]
  exact lineIminusE_mul _ _ _ _

theorem lineP_character {n d j : ℕ}
    (Y M : BinaryMatrix n (d + 1)) :
    lineP j (character Y) M =
      (1 - (2 : ℝ) ^ (j + 1) * lineTranslationMultiplier Y) *
      (1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y) *
        character Y M := by
  unfold lineP lineIminusE
  have hinner (N : BinaryMatrix n (d + 1)) :
      character Y N - (2 : ℝ) ^ j * lineTranslationAverage (character Y) N =
      (1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y) * character Y N := by
    rw [lineTranslationAverage_character]
    ring
  simp_rw [hinner]
  rw [lineTranslationAverage_mul, lineTranslationAverage_character]
  ring

theorem lineP_rankProjection {n d j k : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1)) :
    lineP j (rankProjection k f) M =
      ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n (d + 1))).filter
          (fun Y => Y.rank = k),
        fourierCoeff f Y *
          ((1 - (2 : ℝ) ^ (j + 1) * lineTranslationMultiplier Y) *
            (1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y)) *
          character Y M := by
  unfold rankProjection
  rw [lineP_finset_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [lineP_mul, lineP_character]
  ring

private theorem lineP_scalar_at_adjacent_rank {n d j : ℕ}
    (Y : BinaryMatrix n (d + 1))
    (hr : Y.rank = j ∨ Y.rank = j + 1) :
    (1 - (2 : ℝ) ^ (j + 1) * lineTranslationMultiplier Y) *
      (1 - (2 : ℝ) ^ j * lineTranslationMultiplier Y) =
        if hybridLineSelected Y then 1 else 0 := by
  rw [lineTranslationMultiplier_eq_hybrid]
  by_cases hs : hybridLineSelected Y
  · simp [hs]
  · simp only [if_neg hs]
    rcases hr with hr | hr
    · rw [hr]
      have hp : (2 : ℝ) ^ j * ((2 : ℝ)⁻¹) ^ j = 1 := by
        rw [← mul_pow]
        norm_num
      rw [hp]
      ring
    · rw [hr]
      have hp : (2 : ℝ) ^ (j + 1) * ((2 : ℝ)⁻¹) ^ (j + 1) = 1 := by
        rw [← mul_pow]
        norm_num
      rw [hp]
      ring

/-- On each of the two input ranks that can feed Appendix (A14), the
actual manuscript polynomial `P_{j+1}` equals the hybrid Fourier filter.
This is an input-spectrum equality, before raw restriction and collision
aggregation. -/
theorem lineP_rankProjection_eq_hybridLineFilter {n d j k : ℕ}
    (f : BinaryMatrix n (d + 1) → ℝ)
    (M : BinaryMatrix n (d + 1))
    (hk : k = j ∨ k = j + 1) :
    lineP j (rankProjection k f) M =
      hybridLineFilter (rankProjection k f) M := by
  rw [lineP_rankProjection]
  unfold hybridLineFilter
  simp_rw [fourierCoeff_rankProjection]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hr : Y.rank = k
  · have hradj : Y.rank = j ∨ Y.rank = j + 1 := by
      rcases hk with hj | hj
      · exact Or.inl (hr.trans hj)
      · exact Or.inr (hr.trans hj)
    rw [lineP_scalar_at_adjacent_rank Y hradj]
    by_cases hs : hybridLineSelected Y <;> simp [hr, hs, mul_assoc]
  · simp [hr]

end
end PvNP.RealizableHardness.BinaryMatrixLineTranslation
