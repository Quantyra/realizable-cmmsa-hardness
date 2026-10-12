import PvNP.RealizableHardness.SamplerParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact scalar guards for the separately declared MZ24 count import.
No imported counting result, list-size premise, or extra source assumption is
proved here. These guards retain the inverse-threshold exponent margin.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualMaximalCountGuards

open PvNP.RealizableHardness.SamplerParameters
set_option autoImplicit false
noncomputable section

/-- The actual block count meets even the stronger ambient convention in the
source subsection. The visible-space dimension is supplied by its actual map. -/
theorem blocks_ge_strong_count_dimension {A h : Nat}
    (hA : 1 ≤ A) (hh : 200 ≤ h) : 2 ^ (200 * h) ≤ blocks A h := by
  have hsq : h ^ 2 ≤ A * h ^ 2 := by
    simpa using Nat.mul_le_mul_right (h ^ 2) hA
  have hbase : 200 * h ≤ h ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_right h hh
  have hlin : 200 * h ≤ A * h ^ 2 := hbase.trans hsq
  have hexp : 200 * h ≤ 2 ^ (A * h ^ 2) :=
    hlin.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  exact pow_le_pow_right₀ (by omega) hexp

/-- Every lowered ladder denominator is bounded by one fixed dyadic cost. -/
theorem ladder_denominator_le_dyadic (r : Nat) :
    20 * (5 : Real) ^ r ≤ (2 : Real) ^ (3 * r + 5) := by
  have hpow : (5 : Real) ^ r ≤ (2 : Real) ^ (3 * r) := by
    calc
      (5 : Real) ^ r ≤ ((2 : Real) ^ 3) ^ r :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) r
      _ = (2 : Real) ^ (3 * r) := (pow_mul _ _ _).symm
  calc
    20 * (5 : Real) ^ r ≤ 32 * (2 : Real) ^ (3 * r) :=
      mul_le_mul (by norm_num) hpow (by positivity) (by norm_num)
    _ = (2 : Real) ^ (3 * r + 5) := by rw [pow_add]; norm_num; ring

/-- The one pre-draw C works simultaneously at every actual ladder level. -/
theorem all_ladder_thresholds_meet_count_cutoff
    (rho delta : Real) (r h j : Nat) (hj : j ≤ r) (C : Rat)
    (hmargin : ((3 * r + 5 : Nat) : Real) ≤
      2 * (1000 * rho ^ 2 - delta ^ 3) * (h : Real))
    (hC : (2 : Real) ^ (-2 * (1 - 1000 * rho ^ 2) * (h : Real)) / 5 < (C : Real)) :
    (2 : Real) ^ (-2 * (1 - delta ^ 3) * (h : Real)) <
      ((C / (4 * 5 ^ j) : Rat) : Real) := by
  let e : Real := (2 : Real) ^ (-2 * (1 - 1000 * rho ^ 2) * (h : Real))
  have he : 0 < e := Real.rpow_pos_of_pos (by norm_num) _
  have hexp : -2 * (1 - delta ^ 3) * (h : Real) ≤
      -2 * (1 - 1000 * rho ^ 2) * (h : Real) - ((3 * r + 5 : Nat) : Real) := by
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hexp
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast] at hpow
  have hden := ladder_denominator_le_dyadic r
  have hlevel : 20 * (5 : Real) ^ j ≤ 20 * (5 : Real) ^ r :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (by norm_num)
  have hCdiv : e / (20 * (5 : Real) ^ j) < (C : Real) / (4 * (5 : Real) ^ j) := by
    have hc := div_lt_div_of_pos_right hC (show (0 : Real) < 4 * 5 ^ j by positivity)
    dsimp [e]
    convert hc using 1 <;> field_simp <;> ring
  calc
    (2 : Real) ^ (-2 * (1 - delta ^ 3) * (h : Real)) ≤
        e / (2 : Real) ^ (3 * r + 5) := hpow
    _ ≤ e / (20 * (5 : Real) ^ r) :=
      div_le_div_of_nonneg_left he.le (by positivity) hden
    _ ≤ e / (20 * (5 : Real) ^ j) :=
      div_le_div_of_nonneg_left he.le (by positivity) hlevel
    _ < (C : Real) / (4 * (5 : Real) ^ j) := hCdiv
    _ = ((C / (4 * 5 ^ j) : Rat) : Real) := by push_cast; rfl

/-- A natural same-index floor pays the threshold gap for rho=1/b and
delta=rho/m. No rational threshold is chosen after a question or draw. -/
theorem reciprocal_parameter_threshold_margin {b m r h : Nat}
    (hb : 1 ≤ b) (hm : 1 ≤ m) (hh : b ^ 2 * (3 * r + 5) ≤ h) :
    ((3 * r + 5 : Nat) : Real) ≤
      2 * (1000 * (1 / (b : Real)) ^ 2 -
        ((1 / (b : Real)) / (m : Real)) ^ 3) * (h : Real) := by
  let rho : Real := 1 / (b : Real)
  let delta : Real := rho / (m : Real)
  have hbR : (1 : Real) ≤ b := by exact_mod_cast hb
  have hmR : (1 : Real) ≤ m := by exact_mod_cast hm
  have hbpos : (0 : Real) < b := by linarith
  have hmpos : (0 : Real) < m := by linarith
  have hrho : 0 ≤ rho := by dsimp [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    dsimp [rho]
    exact (div_le_iff₀ hbpos).2 (by simpa using hbR)
  have hdelta : 0 ≤ delta := div_nonneg hrho hmpos.le
  have hdeltarho : delta ≤ rho := by
    dsimp [delta]
    exact (div_le_iff₀ hmpos).2 (by
      simpa using mul_le_mul_of_nonneg_left hmR hrho)
  have hcube : delta ^ 3 ≤ rho ^ 2 := by
    have h3 : delta ^ 3 ≤ rho ^ 3 := pow_le_pow_left₀ hdelta hdeltarho 3
    have hsq : 0 ≤ rho ^ 2 := sq_nonneg rho
    have hmul := mul_le_mul_of_nonneg_right hrho1 hsq
    nlinarith
  have hcoef : rho ^ 2 ≤ 2 * (1000 * rho ^ 2 - delta ^ 3) := by
    nlinarith [sq_nonneg rho]
  have hheight : (b : Real) ^ 2 * ((3 * r + 5 : Nat) : Real) ≤ (h : Real) := by
    exact_mod_cast hh
  have hid : rho ^ 2 * (b : Real) ^ 2 = 1 := by
    dsimp [rho]
    field_simp [ne_of_gt hbpos]
  have hscaled := mul_le_mul_of_nonneg_left hheight (sq_nonneg rho)
  rw [← mul_assoc, hid, one_mul] at hscaled
  exact hscaled.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))

/-- Both quantitative guards use the actual block count and same-index floor.
The source's remaining sufficiently-large-height cutoff is still external. -/
theorem actual_count_import_guards {A b m r h : Nat}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (hh : max 200 (b ^ 2 * (3 * r + 5)) ≤ h) (C : Rat)
    (hC : (2 : Real) ^ (-2 * (1 - 1000 * (1 / (b : Real)) ^ 2) * (h : Real)) / 5 <
      (C : Real)) :
    2 ^ (200 * h) ≤ blocks A h ∧
      ∀ j : Nat, j ≤ r →
        (2 : Real) ^ (-2 * (1 - ((1 / (b : Real)) / (m : Real)) ^ 3) * (h : Real)) <
          ((C / (4 * 5 ^ j) : Rat) : Real) := by
  have h200 : 200 ≤ h := (Nat.le_max_left _ _).trans hh
  have hfloor : b ^ 2 * (3 * r + 5) ≤ h := (Nat.le_max_right _ _).trans hh
  refine ⟨blocks_ge_strong_count_dimension hA h200, ?_⟩
  intro j hj
  exact all_ladder_thresholds_meet_count_cutoff _ _ r h j hj C
    (reciprocal_parameter_threshold_margin hb hm hfloor) hC

end
end PvNP.RealizableHardness.ActualMaximalCountGuards
