import Mathlib.Tactic

/-!
Manuscript parameter order for the modified PCP.

The replacement parameters are `J = 2^(2^(A h^2))` and
`β = A h^2 / J`, so `β J = A h^2`. If `A > (C+10)/κ`, an outer-game
success at most `2^{-κ β J}` sits strictly below a decoded success at
least `2^{-C h^2}`.

The outer-game bound and the decoded-success bound are hypotheses.
This file does not build a star family, a `SeededMap`, or a 3CNF
encoding, and it does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualModifiedPcpParameterOrder

set_option autoImplicit false

/-- Manuscript repetition count `J = 2^(2^(A h^2))`. -/
def repetitionJ (A h : Nat) : Nat :=
  2 ^ (2 ^ (A * h ^ 2))

theorem repetitionJ_pos (A h : Nat) : 0 < repetitionJ A h := by
  unfold repetitionJ
  exact Nat.two_pow_pos _

/-- `β J = A h^2` for `β = A h^2 / J`. -/
theorem beta_mul_repetitionJ (A h : Nat) :
    ((A * h ^ 2 : Rat) / (repetitionJ A h : Rat)) * (repetitionJ A h : Rat) =
      (A * h ^ 2 : Rat) := by
  have hJ : (repetitionJ A h : Rat) ≠ 0 := by
    exact_mod_cast (repetitionJ_pos A h).ne'
  field_simp [hJ]

theorem inv_two_pow_lt {a b : Nat} (h : a < b) :
    ((2 : Rat) ^ b)⁻¹ < ((2 : Rat) ^ a)⁻¹ := by
  have ha : (0 : Rat) < (2 : Rat) ^ a := pow_pos (by norm_num) _
  have hb : (0 : Rat) < (2 : Rat) ^ b := pow_pos (by norm_num) _
  have hpow : (2 : Rat) ^ a < (2 : Rat) ^ b :=
    pow_lt_pow_right₀ (by norm_num : (1 : Rat) < 2) h
  exact (inv_lt_inv₀ hb ha).mpr hpow

/-- Outer success `2^{-κ A h^2}` is strictly below decoded success
`2^{-C h^2}` once `κ A > C + 10` and `h > 0`. -/
theorem parameter_order_contradiction
    (C kappa A h : Nat)
    (hA : C + 10 < kappa * A)
    (hh : 0 < h)
    (decoded outer : Rat)
    (hdec : ((2 : Rat) ^ (C * h ^ 2))⁻¹ ≤ decoded)
    (hout : outer ≤ ((2 : Rat) ^ ((kappa * A) * h ^ 2))⁻¹) :
    outer < decoded := by
  have hsq : 0 < h ^ 2 := by
    have : 0 < h * h := Nat.mul_pos hh hh
    simpa [Nat.pow_two] using this
  have hmidExp : (C + 10) * h ^ 2 < (kappa * A) * h ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hA hsq
  have hsmallExp : C * h ^ 2 < (C + 10) * h ^ 2 :=
    Nat.mul_lt_mul_of_pos_right (by omega) hsq
  have hmid :
      ((2 : Rat) ^ ((kappa * A) * h ^ 2))⁻¹ <
        ((2 : Rat) ^ ((C + 10) * h ^ 2))⁻¹ :=
    inv_two_pow_lt hmidExp
  have hsmall :
      ((2 : Rat) ^ ((C + 10) * h ^ 2))⁻¹ <
        ((2 : Rat) ^ (C * h ^ 2))⁻¹ :=
    inv_two_pow_lt hsmallExp
  exact lt_of_le_of_lt hout (lt_of_lt_of_le (lt_trans hmid hsmall) hdec)

end PvNP.RealizableHardness.ActualModifiedPcpParameterOrder
