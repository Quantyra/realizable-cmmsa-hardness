import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact mathematical sample-size threshold. No concentration or encoded runtime is assumed. -/
namespace PvNP.RealizableHardness.SamplingThreshold

noncomputable def threshold (N : ℕ) (eps : ℝ) : ℝ :=
  ((N : ℝ) * Real.log 2 + Real.log 6) / (2 * (eps / 8) ^ 2)

noncomputable def sampleCount (N : ℕ) (eps : ℝ) : ℕ :=
  2 ^ Nat.clog 2 ⌈threshold N eps⌉₊

theorem threshold_pos (N : ℕ) (eps : ℝ) (heps : 0 < eps) : 0 < threshold N eps := by
  unfold threshold
  apply div_pos
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
      (Real.log_pos (by norm_num))
  · positivity

theorem threshold_gt_one (N : ℕ) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    1 < threshold N eps := by
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6)
  have hN := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  unfold threshold
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (eps / 8) ^ 2)).mpr
  norm_num at hlog
  nlinarith [sq_nonneg (eps - 1)]

theorem sampleCount_pos (N : ℕ) (eps : ℝ) : 0 < sampleCount N eps := by
  unfold sampleCount
  positivity

theorem sampleCount_lower (N : ℕ) (eps : ℝ) : threshold N eps ≤ sampleCount N eps := by
  unfold sampleCount
  apply (Nat.le_ceil _).trans
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) ⌈threshold N eps⌉₊

theorem sampleCount_least (N : ℕ) (eps : ℝ) (j : ℕ)
    (hj : threshold N eps ≤ ((2 ^ j : ℕ) : ℝ)) : sampleCount N eps ≤ 2 ^ j := by
  have hc : ⌈threshold N eps⌉₊ ≤ 2 ^ j := Nat.ceil_le.mpr hj
  have he := (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2 : ℕ))).mpr hc
  exact Nat.pow_le_pow_right (by norm_num) he

theorem sampleCount_upper (N : ℕ) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (sampleCount N eps : ℝ) < 2 * threshold N eps := by
  have hc : 1 < ⌈threshold N eps⌉₊ := Nat.lt_ceil.mpr (by simpa using threshold_gt_one N eps heps heps1)
  have he : 0 < Nat.clog 2 ⌈threshold N eps⌉₊ := Nat.clog_pos (by norm_num) hc
  have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : ℕ)) hc
  have hp : ((2 ^ (Nat.clog 2 ⌈threshold N eps⌉₊).pred : ℕ) : ℝ) < threshold N eps :=
    Nat.lt_ceil.mp hpred
  have hexp : Nat.clog 2 ⌈threshold N eps⌉₊ = (Nat.clog 2 ⌈threshold N eps⌉₊).pred + 1 :=
    (Nat.succ_pred_eq_of_pos he).symm
  unfold sampleCount
  rw [hexp, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- The post-union-bound factor is at most one third; no probability estimate is assumed. -/
theorem failure_budget (N M : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hM : threshold N eps ≤ (M : ℝ)) :
    (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * (eps / 8) ^ 2)) ≤ 1 / 3 := by
  have hd : 0 < 2 * (eps / 8) ^ 2 := by positivity
  have hraw := (div_le_iff₀ hd).mp hM
  have hexp : -2 * (M : ℝ) * (eps / 8) ^ 2 ≤ -((N : ℝ) * Real.log 2 + Real.log 6) := by
    nlinarith only [hraw]
  have hb := Real.exp_le_exp.mpr hexp
  have hid : Real.exp (-((N : ℝ) * Real.log 2 + Real.log 6)) = 1 / ((2 : ℝ) ^ N * 6) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log (by norm_num : (0 : ℝ) < 6)]
    simp only [one_div]
  rw [hid] at hb
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N * 2)
  calc
    _ = ((2 : ℝ) ^ N * 2) * Real.exp (-2 * (M : ℝ) * (eps / 8) ^ 2) := by ring
    _ ≤ ((2 : ℝ) ^ N * 2) * (1 / ((2 : ℝ) ^ N * 6)) := hm
    _ = 1 / 3 := by field_simp; ring

theorem sampleCount_failure_budget (N : ℕ) (eps : ℝ) (heps : 0 < eps) :
    (2 ^ N : ℝ) * (2 * Real.exp (-2 * (sampleCount N eps : ℝ) * (eps / 8) ^ 2)) ≤ 1 / 3 :=
  failure_budget N (sampleCount N eps) eps heps (sampleCount_lower N eps)

theorem threshold_numeric_upper (N : ℕ) (eps : ℝ) (heps : 0 < eps) :
    threshold N eps ≤ 32 * ((N : ℝ) + 5) / eps ^ 2 := by
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
  have hN := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  unfold threshold
  have hid : 2 * (eps / 8) ^ 2 = eps ^ 2 / 32 := by ring
  rw [hid]
  have heq : ((N : ℝ) * Real.log 2 + Real.log 6) / (eps ^ 2 / 32) =
      32 * ((N : ℝ) * Real.log 2 + Real.log 6) / eps ^ 2 := by ring
  rw [heq]
  apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < eps ^ 2)).mpr
  nlinarith

theorem sampleCount_numeric_upper (N : ℕ) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (sampleCount N eps : ℝ) < 64 * ((N : ℝ) + 5) / eps ^ 2 := by
  have h := sampleCount_upper N eps heps heps1
  have hb := threshold_numeric_upper N eps heps
  calc
    _ < 2 * threshold N eps := h
    _ ≤ 2 * (32 * ((N : ℝ) + 5) / eps ^ 2) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

theorem sampleCount_bound_of_inverse_error (N P : ℕ) (eps : ℝ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hInv : 1 / eps ≤ (P : ℝ)) :
    sampleCount N eps ≤ 64 * (N + 5) * P ^ 2 := by
  have hb := sampleCount_numeric_upper N eps heps heps1
  have hi0 : 0 ≤ 1 / eps := by positivity
  have hsq : (1 / eps) ^ 2 ≤ (P : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 64 * ((N : ℝ) + 5))
  have hid : 64 * ((N : ℝ) + 5) / eps ^ 2 = 64 * ((N : ℝ) + 5) * (1 / eps) ^ 2 := by ring
  rw [hid] at hb
  have hout : (sampleCount N eps : ℝ) ≤ 64 * ((N : ℝ) + 5) * (P : ℝ) ^ 2 := le_trans hb.le hm
  exact_mod_cast hout

/-- A general confidence constant gives the exact post-union factor 2/C. -/
theorem failure_budget_of_log_threshold (N M : ℕ) (eps C : ℝ)
    (heps : 0 < eps) (hC : 0 < C)
    (hM : ((N : ℝ) * Real.log 2 + Real.log C) / (2 * (eps / 8) ^ 2) ≤ (M : ℝ)) :
    (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * (eps / 8) ^ 2)) ≤ 2 / C := by
  have hd : 0 < 2 * (eps / 8) ^ 2 := by positivity
  have hraw := (div_le_iff₀ hd).mp hM
  have hexp : -2 * (M : ℝ) * (eps / 8) ^ 2 ≤ -((N : ℝ) * Real.log 2 + Real.log C) := by
    nlinarith only [hraw]
  have hb := Real.exp_le_exp.mpr hexp
  have hid : Real.exp (-((N : ℝ) * Real.log 2 + Real.log C)) = 1 / ((2 : ℝ) ^ N * C) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hC]
    simp only [one_div]
  rw [hid] at hb
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N * 2)
  calc
    _ = ((2 : ℝ) ^ N * 2) * Real.exp (-2 * (M : ℝ) * (eps / 8) ^ 2) := by ring
    _ ≤ ((2 : ℝ) ^ N * 2) * (1 / ((2 : ℝ) ^ N * C)) := hm
    _ = 2 / C := by field_simp <;> ring

/-- The learning corollary reserves half its failure budget by using log 12. -/
noncomputable def learningThreshold (N : ℕ) (eps : ℝ) : ℝ :=
  ((N : ℝ) * Real.log 2 + Real.log 12) / (2 * (eps / 8) ^ 2)

noncomputable def learningSampleCount (N : ℕ) (eps : ℝ) : ℕ :=
  2 ^ Nat.clog 2 ⌈learningThreshold N eps⌉₊

theorem threshold_le_learningThreshold (N : ℕ) (eps : ℝ) :
    threshold N eps ≤ learningThreshold N eps := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 12)
  linarith

theorem learningSampleCount_pos (N : ℕ) (eps : ℝ) : 0 < learningSampleCount N eps := by
  unfold learningSampleCount
  positivity

theorem learningSampleCount_lower (N : ℕ) (eps : ℝ) :
    learningThreshold N eps ≤ learningSampleCount N eps := by
  unfold learningSampleCount
  apply (Nat.le_ceil _).trans
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) ⌈learningThreshold N eps⌉₊

theorem learningSampleCount_least (N : ℕ) (eps : ℝ) (j : ℕ)
    (hj : learningThreshold N eps ≤ ((2 ^ j : ℕ) : ℝ)) : learningSampleCount N eps ≤ 2 ^ j := by
  have hc : ⌈learningThreshold N eps⌉₊ ≤ 2 ^ j := Nat.ceil_le.mpr hj
  have he := (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2 : ℕ))).mpr hc
  exact Nat.pow_le_pow_right (by norm_num) he

theorem learningSampleCount_upper (N : ℕ) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (learningSampleCount N eps : ℝ) < 2 * learningThreshold N eps := by
  have ht : 1 < learningThreshold N eps :=
    lt_of_lt_of_le (threshold_gt_one N eps heps heps1) (threshold_le_learningThreshold N eps)
  have hc : 1 < ⌈learningThreshold N eps⌉₊ := Nat.lt_ceil.mpr (by simpa using ht)
  have he : 0 < Nat.clog 2 ⌈learningThreshold N eps⌉₊ := Nat.clog_pos (by norm_num) hc
  have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : ℕ)) hc
  have hp : ((2 ^ (Nat.clog 2 ⌈learningThreshold N eps⌉₊).pred : ℕ) : ℝ) < learningThreshold N eps :=
    Nat.lt_ceil.mp hpred
  have hexp : Nat.clog 2 ⌈learningThreshold N eps⌉₊ = (Nat.clog 2 ⌈learningThreshold N eps⌉₊).pred + 1 :=
    (Nat.succ_pred_eq_of_pos he).symm
  unfold learningSampleCount
  rw [hexp, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem learning_failure_budget (N M : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hM : learningThreshold N eps ≤ (M : ℝ)) :
    (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * (eps / 8) ^ 2)) ≤ 1 / 6 := by
  have h := failure_budget_of_log_threshold N M eps 12 heps (by norm_num) hM
  calc
    _ ≤ (2 : ℝ) / 12 := h
    _ = 1 / 6 := by norm_num

theorem learningSampleCount_failure_budget (N : ℕ) (eps : ℝ) (heps : 0 < eps) :
    (2 ^ N : ℝ) * (2 * Real.exp (-2 * (learningSampleCount N eps : ℝ) * (eps / 8) ^ 2)) ≤ 1 / 6 :=
  learning_failure_budget N (learningSampleCount N eps) eps heps (learningSampleCount_lower N eps)

theorem learningThreshold_numeric_upper (N : ℕ) (eps : ℝ) (heps : 0 < eps) :
    learningThreshold N eps ≤ 32 * ((N : ℝ) + 11) / eps ^ 2 := by
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h12 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
  have hN := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  unfold learningThreshold
  have hid : 2 * (eps / 8) ^ 2 = eps ^ 2 / 32 := by ring
  rw [hid]
  have heq : ((N : ℝ) * Real.log 2 + Real.log 12) / (eps ^ 2 / 32) =
      32 * ((N : ℝ) * Real.log 2 + Real.log 12) / eps ^ 2 := by ring
  rw [heq]
  apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < eps ^ 2)).mpr
  nlinarith

theorem learningSampleCount_numeric_upper (N : ℕ) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (learningSampleCount N eps : ℝ) < 64 * ((N : ℝ) + 11) / eps ^ 2 := by
  have h := learningSampleCount_upper N eps heps heps1
  have hb := learningThreshold_numeric_upper N eps heps
  calc
    _ < 2 * learningThreshold N eps := h
    _ ≤ 2 * (32 * ((N : ℝ) + 11) / eps ^ 2) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

theorem learningSampleCount_bound_of_inverse_error (N P : ℕ) (eps : ℝ)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hInv : 1 / eps ≤ (P : ℝ)) :
    learningSampleCount N eps ≤ 64 * (N + 11) * P ^ 2 := by
  have hb := learningSampleCount_numeric_upper N eps heps heps1
  have hi0 : 0 ≤ 1 / eps := by positivity
  have hsq : (1 / eps) ^ 2 ≤ (P : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 64 * ((N : ℝ) + 11))
  have hid : 64 * ((N : ℝ) + 11) / eps ^ 2 = 64 * ((N : ℝ) + 11) * (1 / eps) ^ 2 := by ring
  rw [hid] at hb
  have hout : (learningSampleCount N eps : ℝ) ≤ 64 * ((N : ℝ) + 11) * (P : ℝ) ^ 2 := le_trans hb.le hm
  exact_mod_cast hout

end PvNP.RealizableHardness.SamplingThreshold
