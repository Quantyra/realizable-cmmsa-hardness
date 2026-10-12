import PvNP.RealizableHardness.ActualNumericRobustReal
import PvNP.RealizableHardness.DropTailParameters
import Mathlib.Tactic

/-! Exact scalar absorption for the original global favorable-mass route.
The probability and game-law identifications are separate obligations.
UNCOMPILED source candidate, with explicit same-height guards. -/
namespace PvNP.RealizableHardness.ActualGlobalDecoderScalar

open ActualNumericRobustReal ActualStarAcceptedGoodMass
open ActualStarFixedRhoDimensionGuard DropTailParameters

set_option autoImplicit false
noncomputable section

/-- The actual global posterior expression, after paying all three charges. -/
def posteriorFloor (m r h : Nat) (C : Real) : Real :=
  (decay 6 h / (r + 1) * (8 * (successMargin (badExponent m h) : Real)) -
    decay 20 h - decay 69 h - decay 20 h / 3) * (C / 4)

private theorem half_pow_antitone {p q : Nat} (hpq : p ≤ q) :
    (1 / 2 : Real) ^ q ≤ (1 / 2 : Real) ^ p :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) hpq

private theorem actual_margin_lower (m h : Nat) :
    (1 / 2 : Real) ^ (2 * m * h) ≤ (successMargin (badExponent m h) : Real) := by
  have hE : badExponent m h ≤ 2 * m * h := by
    unfold badExponent
    exact Nat.mul_le_mul_left (2 * m) (Nat.sub_le _ _)
  simpa [successMargin, one_div, inv_pow] using half_pow_antitone hE

/-- The fixed threshold e/5<C gives a linear-height dyadic lower bound on C. -/
theorem actual_threshold_lower (m h : Nat) {C : Real}
    (hC : refreshThreshold m h / 5 < C) :
    (1 / 2 : Real) ^ (2 * h + 3) ≤ C := by
  have hexp : -((2 * h : Nat) : Real) ≤
      -2 * (1 - 1000 * (1 / (ActualCmmsaParameterReconciliation.bOf m : Real)) ^ 2) *
        (h : Real) := by
    push_cast
    have hn := mul_nonneg
      (sq_nonneg (1 / (ActualCmmsaParameterReconciliation.bOf m : Real)))
      (Nat.cast_nonneg h : (0 : Real) ≤ h)
    nlinarith
  have he : (1 / 2 : Real) ^ (2 * h) ≤ refreshThreshold m h := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hexp
    simpa [refreshThreshold, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2),
      Real.rpow_natCast, one_div, inv_pow] using hp
  calc
    (1 / 2 : Real) ^ (2 * h + 3) = (1 / 2 : Real) ^ (2 * h) / 8 := by
      norm_num [pow_add] <;> ring
    _ ≤ (1 / 2 : Real) ^ (2 * h) / 5 := by
      have hp : 0 ≤ (1 / 2 : Real) ^ (2 * h) := by positivity
      linarith
    _ ≤ refreshThreshold m h / 5 := div_le_div_of_nonneg_right he (by norm_num)
    _ ≤ C := hC.le

/-- The global favorable mass, including its dimension cost, absorbs the
actual posterior charges. Linear threshold costs are kept until the last step. -/
theorem actual_posterior_floor_lower {m r h : Nat} {C : Real}
    (hr : r ≤ h) (hh : 2 * m + 4 ≤ h)
    (hC : refreshThreshold m h / 5 < C) :
    decay 7 h ≤ posteriorFloor m r h C := by
  let S : Real := successMargin (badExponent m h)
  let X : Real := S * decay 6 h / (r + 1)
  have hS : (1 / 2 : Real) ^ (2 * m * h) ≤ S := actual_margin_lower m h
  have hSpos : 0 < S := by dsimp [S, successMargin]; positivity
  have hXpos : 0 < X := by dsimp [X]; exact div_pos (mul_pos hSpos (decay_pos 6 h)) (by positivity)
  have hdenNat : r + 1 ≤ 2 ^ h := by
    have hp : h < 2 ^ h := Nat.lt_two_pow_self
    omega
  have hden : ((r : Real) + 1) ≤ (2 : Real) ^ h := by exact_mod_cast hdenNat
  have hinv : (1 / 2 : Real) ^ h ≤ 1 / ((r : Real) + 1) := by
    have hi := div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 1)
      (by positivity : (0 : Real) < (r : Real) + 1) hden
    simpa [one_div, inv_pow] using hi
  have hXlinear : (1 / 2 : Real) ^ (6 * h ^ 2 + (2 * m + 1) * h) ≤ X := by
    have hp := mul_le_mul hS hinv (by positivity) hSpos.le
    have hp' := mul_le_mul_of_nonneg_right hp (decay_pos 6 h).le
    calc
      _ = ((1 / 2 : Real) ^ (2 * m * h) * (1 / 2 : Real) ^ h) * decay 6 h := by
        rw [show 6 * h ^ 2 + (2 * m + 1) * h = (2 * m * h + h) + 6 * h ^ 2 by ring]
        simp only [pow_add, decay]
      _ ≤ S * (1 / ((r : Real) + 1)) * decay 6 h := hp'
      _ = X := by dsimp [X]; ring
  have hexp : 6 * h ^ 2 + (2 * m + 1) * h ≤ 7 * h ^ 2 := by
    have hm := Nat.mul_le_mul_right h hh
    nlinarith
  have hX : decay 7 h ≤ X := (half_pow_antitone hexp).trans hXlinear
  have h20 : decay 20 h ≤ X := (half_pow_antitone
    (show 7 * h ^ 2 ≤ 20 * h ^ 2 by omega)).trans hX
  have h69 : decay 69 h ≤ X := (half_pow_antitone
    (show 7 * h ^ 2 ≤ 69 * h ^ 2 by omega)).trans hX
  have hcharge : decay 20 h + decay 69 h + decay 20 h / 3 ≤ 4 * X := by
    linarith [hXpos]
  have hClower := actual_threshold_lower m h hC
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hClower
  have hpaid : X * C ≤ posteriorFloor m r h C := by
    have hp := mul_le_mul_of_nonneg_right hcharge hCpos.le
    have hid : posteriorFloor m r h C =
        (8 * X - (decay 20 h + decay 69 h + decay 20 h / 3)) * (C / 4) := by
      dsimp [posteriorFloor, X, S]
      ring
    rw [hid]
    nlinarith
  have hprod : (1 / 2 : Real) ^ (6 * h ^ 2 + (2 * m + 3) * h + 3) ≤ X * C := by
    have hp := mul_le_mul hXlinear hClower (by positivity) hXpos.le
    calc
      _ = (1 / 2 : Real) ^ (6 * h ^ 2 + (2 * m + 1) * h) *
          (1 / 2 : Real) ^ (2 * h + 3) := by
        rw [← pow_add]
        congr 1
        ring
      _ ≤ X * C := hp
  have hexp' : 6 * h ^ 2 + (2 * m + 3) * h + 3 ≤ 7 * h ^ 2 := by
    have hm := Nat.mul_le_mul_right h hh
    have hh3 : 3 ≤ h := by omega
    nlinarith
  exact ((half_pow_antitone hexp').trans hprod).trans hpaid

/-- The full supplied-vector correction is paid once at the same height. -/
theorem actual_full_vector_loss_le {r J h : Nat} (hJ : r + 100 * h ^ 2 ≤ J) :
    (2 : Real) ^ r / (2 : Real) ^ J ≤ decay 100 h := by
  have hpow : (2 : Real) ^ (r + 100 * h ^ 2) ≤ (2 : Real) ^ J :=
    pow_le_pow_right₀ (by norm_num) hJ
  calc
    _ ≤ (2 : Real) ^ r / (2 : Real) ^ (r + 100 * h ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = decay 100 h := by
      rw [pow_add, decay_eq_reciprocal]
      field_simp

/-- One quadratic exponent pays the vector loss after the posterior bound. -/
theorem actual_posterior_floor_sub_vector_lower {m r J h : Nat} {C : Real}
    (hr : r ≤ h) (hh : 2 * m + 4 ≤ h)
    (hC : refreshThreshold m h / 5 < C) (hJ : r + 100 * h ^ 2 ≤ J) :
    decay 8 h ≤ posteriorFloor m r h C - (2 : Real) ^ r / (2 : Real) ^ J := by
  have hpost := actual_posterior_floor_lower hr hh hC
  have hloss := actual_full_vector_loss_le hJ
  have hh1 : 1 ≤ h := by omega
  have hsq : 1 ≤ h ^ 2 := one_le_pow₀ hh1
  have hhalf : decay 1 h ≤ (1 / 2 : Real) := by
    simpa [decay] using half_pow_antitone hsq
  have h8 : decay 8 h ≤ decay 7 h / 2 := by
    have hp := mul_le_mul_of_nonneg_left hhalf (decay_pos 7 h).le
    have he := decay_add 7 1 h
    norm_num at he
    rw [he]
    linarith
  have h100 : decay 100 h ≤ decay 8 h := half_pow_antitone
    (show 8 * h ^ 2 ≤ 100 * h ^ 2 by omega)
  linarith

end
end PvNP.RealizableHardness.ActualGlobalDecoderScalar
