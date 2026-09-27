import PvNP.RealizableHardness.ActualDinurGapHalf
import PvNP.RealizableHardness.StarListDecoding

/-!
Repetition count for Dinur's gap at the fixed star arity `certifiedM`.

`certifiedMDinurReps` is chosen after that arity so that
`(8 * manuscriptSigma L)^{certifiedM L + 1} * (1 - amplifier.gap)^t ≤ 5/8`.
The positive gap makes `1 - gap < 1`, which is why some finite `t` exists.

A star of arity `certifiedM L` reads at most `certifiedM L + 1` vertices.
For large `L` every repetition count that meets the ceiling is strictly
longer than that, so the count cannot be realized by giving each repetition
its own vertex inside the star.

This file does not build that star family, a `SeededMap`, or a
`Preserves (1/6)` map. `hSrcCmmsa` stays.
-/
namespace PvNP.RealizableHardness.ActualCertifiedMDinurReps

open Complexity
open Dinur
open ActualCertifiedManuscriptParameters
open ActualDinurGapHalf
open ActualFpMapInterface
open ActualHeadlineParameters
open StarListDecoding

set_option autoImplicit false

theorem certifiedM_dinur_repetition_exists (E : ExpanderFamily) (L : Nat) :
    ∃ t : ℕ,
      (8 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) *
        (1 - (amplifier E).gap) ^ t ≤ (5 : ℚ) / 8 := by
  set r : ℚ := 1 - (amplifier E).gap
  have hr0 : 0 ≤ r := by
    have hle : (amplifier E).gap ≤ 1 := (amplifier E).gap_le_one
    linarith
  have hr1 : r < 1 := by
    have hpos : 0 < (amplifier E).gap := (amplifier E).gap_pos
    linarith
  set s : ℚ := 8 * (manuscriptSigma L : ℚ)
  by_cases hs0 : s = 0
  · refine ⟨0, ?_⟩
    have hm : certifiedM L + 1 ≠ 0 := by omega
    rw [hs0, zero_pow hm, zero_mul]
    norm_num
  · have hspos : 0 < s := by
      have hsnonneg : 0 ≤ s := by
        dsimp [s]
        positivity
      exact lt_of_le_of_ne hsnonneg (Ne.symm hs0)
    have hden : 0 < s ^ (certifiedM L + 1) := pow_pos hspos _
    have hc : 0 < ((5 : ℚ) / 8) / s ^ (certifiedM L + 1) :=
      div_pos (by norm_num) hden
    obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hc hr1
    refine ⟨t, ?_⟩
    have hmul : s ^ (certifiedM L + 1) * r ^ t < (5 : ℚ) / 8 := by
      rw [mul_comm]
      exact (lt_div_iff₀ hden).mp ht
    have _hr0 : 0 ≤ r ^ t := pow_nonneg hr0 t
    exact le_of_lt hmul

noncomputable def certifiedMDinurReps (E : ExpanderFamily) (L : Nat) : Nat :=
  Classical.choose (certifiedM_dinur_repetition_exists E L)

theorem certifiedMDinurReps_spec (E : ExpanderFamily) (L : Nat) :
    (8 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) *
      (1 - (amplifier E).gap) ^ certifiedMDinurReps E L ≤ (5 : ℚ) / 8 :=
  Classical.choose_spec (certifiedM_dinur_repetition_exists E L)

theorem support_card_le {V : Type*} {Sigma : V → Type*} {m : ℕ}
    (e : Star V Sigma m) : e.support.card ≤ m + 1 := by
  classical
  calc
    e.support.card = (Finset.univ.image e.slot).card := by simp [Star.support]
    _ ≤ (Finset.univ : Finset (Fin (m + 1))).card := Finset.card_image_le
    _ = m + 1 := by simp

theorem dinur_hn_repetition_exceeds_arity (E : ExpanderFamily) :
    ∃ L0, ∀ L, L0 ≤ L → ∀ t : ℕ,
      (8 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) *
          (1 - (amplifier E).gap) ^ t ≤ (5 : ℚ) / 8 →
        certifiedM L + 1 < t := by
  obtain ⟨L0, hL0⟩ := manuscriptSigma_ge_pow1013
  refine ⟨L0, ?_⟩
  intro L hL t hle
  set r : ℚ := 1 - (amplifier E).gap
  have hr0 : 0 ≤ r := by
    have hle1 : (amplifier E).gap ≤ 1 := (amplifier E).gap_le_one
    linarith
  have hr1 : r ≤ 1 := by
    have hr0' : 0 ≤ (amplifier E).gap := (amplifier E).gap_pos.le
    linarith
  have hrhalf : (1 : ℚ) / 2 ≤ r := one_sub_dinur_gap_ge_half E
  by_contra ht
  have htle : t ≤ certifiedM L + 1 := by omega
  have hpow : r ^ (certifiedM L + 1) ≤ r ^ t :=
    pow_le_pow_of_le_one hr0 hr1 htle
  set s : ℚ := 8 * (manuscriptSigma L : ℚ)
  have hprod : (4 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) ≤
      s ^ (certifiedM L + 1) * r ^ t := by
    have hhalf : (4 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) ≤
        (s * r) ^ (certifiedM L + 1) := by
      have h4 : 4 * (manuscriptSigma L : ℚ) ≤ s * r := by
        dsimp [s]
        have hσ0 : 0 ≤ (manuscriptSigma L : ℚ) := Nat.cast_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hrhalf
          (mul_nonneg (by norm_num : (0 : ℚ) ≤ 8) hσ0)
        have hid : 8 * (manuscriptSigma L : ℚ) * ((1 : ℚ) / 2) =
            4 * (manuscriptSigma L : ℚ) := by ring
        linarith
      exact pow_le_pow_left₀ (by positivity) h4 _
    have hfactor : (s * r) ^ (certifiedM L + 1) ≤ s ^ (certifiedM L + 1) * r ^ t := by
      have hs0 : 0 ≤ s := by
        dsimp [s]
        positivity
      calc
        (s * r) ^ (certifiedM L + 1) = s ^ (certifiedM L + 1) * r ^ (certifiedM L + 1) := by
          rw [mul_pow]
        _ ≤ s ^ (certifiedM L + 1) * r ^ t :=
          mul_le_mul_of_nonneg_left hpow (pow_nonneg hs0 _)
    exact le_trans hhalf hfactor
  have hσ : (2 ^ 1013 : ℚ) ≤ (manuscriptSigma L : ℚ) := by exact_mod_cast hL0 L hL
  have hone2 : (1 : ℚ) ≤ (2 ^ 1013 : ℚ) := by
    exact_mod_cast (Nat.one_le_two_pow : (1 : ℕ) ≤ 2 ^ 1013)
  have h4σ : (1 : ℚ) ≤ 4 * (manuscriptSigma L : ℚ) := by
    have honeσ : (1 : ℚ) ≤ (manuscriptSigma L : ℚ) := le_trans hone2 hσ
    have h4 : (4 : ℚ) ≤ 4 * (manuscriptSigma L : ℚ) :=
      le_mul_of_one_le_right (by norm_num) honeσ
    exact le_trans (by norm_num : (1 : ℚ) ≤ 4) h4
  have hself : 4 * (manuscriptSigma L : ℚ) ≤
      (4 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) := by
    have hpow1 : (4 * (manuscriptSigma L : ℚ)) ^ 1 ≤
        (4 * (manuscriptSigma L : ℚ)) ^ (certifiedM L + 1) :=
      pow_le_pow_right₀ h4σ (Nat.succ_le_succ (Nat.zero_le _))
    simpa using hpow1
  have h58 : (5 : ℚ) / 8 < 4 * (manuscriptSigma L : ℚ) :=
    lt_of_lt_of_le (by norm_num : (5 : ℚ) / 8 < 1) h4σ
  have hgt : (5 : ℚ) / 8 < s ^ (certifiedM L + 1) * r ^ t :=
    lt_of_lt_of_le (lt_of_lt_of_le h58 hself) hprod
  exact not_le_of_gt hgt hle

theorem certifiedMDinurReps_exceeds_arity (E : ExpanderFamily) :
    ∃ L0, ∀ L, L0 ≤ L → certifiedM L + 1 < certifiedMDinurReps E L := by
  obtain ⟨L0, hL0⟩ := dinur_hn_repetition_exceeds_arity E
  refine ⟨L0, ?_⟩
  intro L hL
  exact hL0 L hL _ (certifiedMDinurReps_spec E L)

end PvNP.RealizableHardness.ActualCertifiedMDinurReps
