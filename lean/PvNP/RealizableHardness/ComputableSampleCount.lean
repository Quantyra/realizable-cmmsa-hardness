import PvNP.RealizableHardness.SamplingThreshold

/-! A conservative computable count; numerical bounds are not machine runtime bounds. -/
namespace PvNP.RealizableHardness.ComputableSampleCount
open SamplingThreshold

def target (N P : Nat) : Nat := 32 * (N + 11) * P ^ 2
def exponent (N P : Nat) : Nat := Nat.clog 2 (target N P)
def count (N P : Nat) : Nat := 2 ^ exponent N P

theorem count_pos (N P : Nat) : 0 < count N P := by
  unfold count
  positivity

theorem count_power_two (N P : Nat) : count N P = 2 ^ exponent N P := rfl

theorem target_le_count (N P : Nat) : target N P <= count N P :=
  Nat.le_pow_clog (by norm_num) _

theorem target_gt_one (N P : Nat) (hP : 0 < P) : 1 < target N P := by
  have hsq : 1 <= P ^ 2 := by nlinarith
  unfold target
  nlinarith

theorem count_upper (N P : Nat) (hP : 0 < P) : count N P < 64 * (N + 11) * P ^ 2 := by
  have ht := target_gt_one N P hP
  have he : 0 < Nat.clog 2 (target N P) := Nat.clog_pos (by norm_num) ht
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : Nat)) ht
  have hexp : Nat.clog 2 (target N P) = (Nat.clog 2 (target N P)).pred + 1 :=
    (Nat.succ_pred_eq_of_pos he).symm
  unfold count exponent
  rw [hexp, pow_succ]
  unfold target at *
  nlinarith

theorem learningThreshold_le_target (N P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) :
    learningThreshold N eps <= (target N P : Real) := by
  have hb := learningThreshold_numeric_upper N eps heps
  have hi0 : 0 <= 1 / eps := by positivity
  have hsq : (1 / eps) ^ 2 <= (P : Real) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq
    (by positivity : (0 : Real) <= 32 * ((N : Real) + 11))
  have hid : 32 * ((N : Real) + 11) / eps ^ 2 =
    32 * ((N : Real) + 11) * (1 / eps) ^ 2 := by ring
  rw [hid] at hb
  have hout := hb.trans hm
  simpa [target] using hout

theorem learningThreshold_le_count (N P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) :
    learningThreshold N eps <= (count N P : Real) := by
  apply (learningThreshold_le_target N P eps heps hInv).trans
  exact_mod_cast target_le_count N P

theorem threshold_le_count (N P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) :
    threshold N eps <= (count N P : Real) :=
  (threshold_le_learningThreshold N eps).trans (learningThreshold_le_count N P eps heps hInv)

theorem inverse_bound_pos (P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) : 0 < P := by
  have h : (0 : Real) < P := lt_of_lt_of_le (by positivity : (0 : Real) < 1 / eps) hInv
  exact_mod_cast h

theorem count_upper_of_inverse (N P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) :
    count N P < 64 * (N + 11) * P ^ 2 :=
  count_upper N P (inverse_bound_pos P eps heps hInv)

theorem learning_budget (N P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) :
    (2 ^ N : Real) * (2 * Real.exp (-2 * (count N P : Real) * (eps / 8) ^ 2)) <= 1 / 6 :=
  learning_failure_budget N (count N P) eps heps (learningThreshold_le_count N P eps heps hInv)

theorem base_budget (N P : Nat) (eps : Real)
    (heps : 0 < eps) (hInv : 1 / eps <= (P : Real)) :
    (2 ^ N : Real) * (2 * Real.exp (-2 * (count N P : Real) * (eps / 8) ^ 2)) <= 1 / 3 :=
  failure_budget N (count N P) eps heps (threshold_le_count N P eps heps hInv)

end PvNP.RealizableHardness.ComputableSampleCount

