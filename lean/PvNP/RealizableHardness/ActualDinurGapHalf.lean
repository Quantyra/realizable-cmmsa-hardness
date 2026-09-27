import Complexitylib.Classes.PCP.Internal.Dinur
import PvNP.RealizableHardness.ActualDinurArityGap

/-!
Dinur's chosen gap is at most `1/2`, so `1 - gap` is a half-base.

`half_base_repetition_misses_hn` then says that the ceiling
`(1 - amplifier.gap)^t` misses
`(8 * manuscriptSigma L)^{t+1} * r^t ≤ 5/8` for every repetition count.
An arity-`t` star family cannot use that ceiling at `manuscriptSigma`.

`gap₀` stays positive, so `1 - gap < 1`. `fixed_arity_base_meets_hn` still
gives numerical room when the exponent stays `certifiedM L + 1` and the
repetition count is chosen afterward. This file does not build that star
family, a `SeededMap`, or a `Preserves (1/6)` map.
-/
namespace PvNP.RealizableHardness.ActualDinurGapHalf

open Complexity
open Dinur
open ActualDinurArityGap

set_option autoImplicit false

theorem powT_eight (q : ℕ) : powT K q = 8 * K * (q - 1) := by
  unfold powT
  ring

theorem dinur_powFloor_le_half (q : ℕ) (hq : 2 ≤ q) (lam : ℝ) (hlam : lam < 1) :
    RegCSP.powFloor (RegCSP.powConst q DinurAlpha) (powT K q) lam ≤ (1 : ℝ) / 2 := by
  set c : ℝ := RegCSP.powConst q DinurAlpha
  set T : ℝ := (powT K q : ℝ)
  have hsub : 0 < 1 - lam := sub_pos.mpr hlam
  have hK : (1 : ℕ) ≤ K := one_le_K
  have hq1 : 1 ≤ q - 1 := by omega
  have hqm : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    have honeq : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
    rw [Nat.cast_sub honeq]
    simp
  have hKposNat : 0 < K := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hK
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr hKposNat
  have hTnat : 0 < powT K q := by
    rw [powT_eight]
    exact Nat.mul_pos (Nat.mul_pos (by decide : 0 < 8) hK) hq1
  have hT : 0 < T := Nat.cast_pos.mpr hTnat
  have hc0 : 0 ≤ c := by
    dsimp [c]
    rw [RegCSP.powConst]
    refine div_nonneg ?_ ?_
    · rw [← hqm]
      exact Nat.cast_nonneg _
    · exact mul_nonneg (by norm_num) (sq_nonneg _)
  have htail : 0 ≤ 2 * T / (1 - lam) :=
    div_nonneg (mul_nonneg (by norm_num) hT.le) hsub.le
  have hden_ge : 2 * T ^ 2 ≤ c + 2 * T ^ 2 + 2 * T / (1 - lam) := by
    linarith [hc0, htail]
  have hT2pos : 0 < 2 * T ^ 2 := mul_pos (by norm_num) (pow_pos hT 2)
  have hdenpos : 0 < c + 2 * T ^ 2 + 2 * T / (1 - lam) := by
    linarith [hT2pos, hc0, htail]
  have hnum : 0 ≤ c ^ 2 / T ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfloor : RegCSP.powFloor c T lam ≤ (c ^ 2 / T ^ 2) / (2 * T ^ 2) := by
    rw [RegCSP.powFloor]
    exact div_le_div_of_nonneg_left hnum hT2pos hden_ge
  have hquot : (c ^ 2 / T ^ 2) / (2 * T ^ 2) = c ^ 2 / (2 * T ^ 4) := by ring
  have hTeq : T = 8 * (K : ℝ) * ((q - 1 : ℕ) : ℝ) := by
    dsimp [T]
    rw [powT_eight, Nat.cast_mul, Nat.cast_mul]
    simp
  have hqR : 0 ≤ (q : ℝ) - 1 := by
    rw [← hqm]
    exact Nat.cast_nonneg _
  have hcLe : c ≤ (q : ℝ) - 1 := by
    dsimp [c]
    rw [RegCSP.powConst, ← hqm]
    have hden : (1 : ℝ) ≤ 4 * (K : ℝ) ^ 2 := by
      have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
      have hsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by
        rw [pow_two, ← one_mul (1 : ℝ)]
        exact mul_le_mul hK1 hK1 (by norm_num) hKpos.le
      linarith
    exact div_le_self (Nat.cast_nonneg _) hden
  have hqLeT : (q : ℝ) - 1 ≤ T := by
    rw [hTeq, ← hqm]
    have h8 : (1 : ℝ) ≤ 8 * (K : ℝ) := by
      have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
      linarith
    have hnonneg : 0 ≤ ((q - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right h8 hnonneg
    simpa [mul_assoc] using hmul
  have hT1 : (1 : ℝ) ≤ T := by
    have hq1R : (1 : ℝ) ≤ (q : ℝ) - 1 := by
      rw [← hqm]
      exact_mod_cast hq1
    exact le_trans hq1R hqLeT
  have hTsq : T ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT1 hT.le
    simpa [pow_two, mul_comm] using this
  have hcT : c ≤ T ^ 2 := le_trans (le_trans hcLe hqLeT) hTsq
  have hpow : c ^ 2 ≤ T ^ 4 := by
    have hcs : c ^ 2 ≤ (T ^ 2) ^ 2 := pow_le_pow_left₀ hc0 hcT 2
    have hid : (T ^ 2) ^ 2 = T ^ (2 * 2) := by rw [← pow_mul]
    have hfour : T ^ (2 * 2) = T ^ 4 := by simp
    rw [← hfour, ← hid]
    exact hcs
  have hT4 : 0 < 2 * T ^ 4 := mul_pos (by norm_num) (pow_pos hT 4)
  have hhalf : c ^ 2 / (2 * T ^ 4) ≤ (1 : ℝ) / 2 := by
    have hmul : c ^ 2 ≤ T ^ 4 := hpow
    have hscaled : c ^ 2 ≤ (1 / 2) * (2 * T ^ 4) := by
      have hid : (1 / 2) * (2 * T ^ 4) = T ^ 4 := by ring
      rw [hid]
      exact hmul
    exact (div_le_iff₀ hT4).mpr hscaled
  exact hfloor.trans (by rw [hquot]; exact hhalf)

theorem dinur_gap_le_half (E : ExpanderFamily) : gap₀ E ≤ (1 : ℚ) / 2 := by
  have hfloor : floor₀ E ≤ (1 : ℝ) / 2 := by
    rw [floor₀]
    exact dinur_powFloor_le_half (q₀ E) (two_le_q₀ E) (ConstraintGraph.preprocessLam E)
      (ConstraintGraph.preprocessLam_lt_one E)
  have hgap : ((gap₀ E : ℚ) : ℝ) ≤ floor₀ E / 704 := gap₀_le E
  have h704 : floor₀ E / 704 ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 704)]
    nlinarith [hfloor]
  have hreal : ((gap₀ E : ℚ) : ℝ) ≤ (1 : ℝ) / 2 := le_trans hgap h704
  have htwoReal : ((2 * gap₀ E : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
    rw [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one]
    have hmul := mul_le_mul_of_nonneg_left hreal (by norm_num : (0 : ℝ) ≤ 2)
    have hid : (2 : ℝ) * ((1 : ℝ) / 2) = 1 := by ring
    rw [← hid]
    exact hmul
  have htwo : 2 * gap₀ E ≤ 1 := Rat.cast_le.mp htwoReal
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr (by simpa [mul_comm] using htwo)

theorem one_sub_dinur_gap_ge_half (E : ExpanderFamily) :
    (1 : ℚ) / 2 ≤ 1 - (amplifier E).gap := by
  have hgap : (amplifier E).gap ≤ (1 : ℚ) / 2 := by
    simpa [amplifier] using dinur_gap_le_half E
  linarith

theorem dinur_power_ceiling_misses_hn (E : ExpanderFamily) :
    ∃ L0, ∀ L, L0 ≤ L → ∀ t : ℕ,
      ¬ ((8 * (ActualHeadlineParameters.manuscriptSigma L : ℚ)) ^ (t + 1) *
            (1 - (amplifier E).gap) ^ t ≤
          (5 : ℚ) / 8) :=
  half_base_repetition_misses_hn (1 - (amplifier E).gap) (one_sub_dinur_gap_ge_half E)

end PvNP.RealizableHardness.ActualDinurGapHalf
