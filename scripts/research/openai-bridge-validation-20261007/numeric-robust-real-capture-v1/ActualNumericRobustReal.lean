import PvNP.RealizableHardness.ActualNumericRobustCutoffs
import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Real robust-local cutoffs at the existing numeric floor.
These arithmetic candidates do not construct a refresh history or a decoder. -/
namespace PvNP.RealizableHardness.ActualNumericRobustReal

open ActualNumericRobustCutoffs ActualNumericExplicitHeight ActualNumericSourceHeight
open ActualCmmsaParameterReconciliation SamplerParameters

set_option autoImplicit false
noncomputable section

def refreshThreshold (m h : Nat) : Real :=
  (2 : Real) ^ (-2 * (1 - 1000 * (1 / (bOf m : Real)) ^ 2) * (h : Real))

def refreshHorizon (r n : Nat) (e : Real) : Nat :=
  Nat.ceil (8 * (2 : Real) ^ (r * n) / e) + 1

def refreshExponent (h r n : Nat) : Nat :=
  (2 * h - r) * (n - r - 2 * h) + 2 - 4 * h

def refreshFailureBound (h r n : Nat) : Real :=
  16 * ((r : Real) + 1) ^ 2 * (2 : Real) ^ (n * (r + 1)) *
    Real.exp (-((2 : Real) ^ refreshExponent h r n) / 12)

private theorem square_le_two_pow {k : Nat} (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [pow_succ]
      have hquad : 2 * k + 1 ≤ k ^ 2 := by
        nlinarith [Nat.mul_le_mul_left k hk]
      nlinarith [hquad]

private theorem exponent_guards {h r n : Nat}
    (hh : 16 ≤ h) (hr : 8 * (r + 1) ≤ h)
    (hn : 8 * h + 4 * r + 16 ≤ n) :
    4 ≤ refreshExponent h r n ∧
    h * n ≤ 2 * refreshExponent h r n ∧
    n * (2 * r + 1) + 2 * h + 2 * r + 9 ≤ 3 * (h * n) ∧
    256 ≤ h * n := by
  let u := 2 * h - r
  let v := n - r - 2 * h
  have hu : h ≤ u := by dsimp [u]; omega
  have hv : n + 16 ≤ 2 * v := by dsimp [v]; omega
  have hv16 : 16 ≤ v := by dsimp [v]; omega
  have hmul := Nat.mul_le_mul hu hv
  have hprod : 4 * h ≤ u * v + 2 := by
    have hp := Nat.mul_le_mul hu hv16
    nlinarith [hp]
  have hE : refreshExponent h r n + 4 * h = u * v + 2 := by
    exact Nat.sub_add_cancel hprod
  have hhalf : h * n ≤ 2 * refreshExponent h r n := by
    nlinarith [hmul, hE]
  have h256 : 256 ≤ h * n := by
    have hn16 : 16 ≤ n := by omega
    nlinarith [Nat.mul_le_mul hh hn16]
  have hK : n * (2 * r + 1) + 2 * h + 2 * r + 9 ≤ 3 * (h * n) := by
    have hrh : r ≤ h := by omega
    have hnr := Nat.mul_le_mul_left n hrh
    have hremain := Nat.mul_le_mul (show 2 ≤ h - 1 by omega) hn
    have hsub : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
    have hsubn := congrArg (fun z : Nat => z * n) hsub
    nlinarith [hnr, hremain, hsubn]
  exact ⟨by omega, hhalf, hK, h256⟩

private theorem horizon_le {h r n : Nat} {e : Real}
    (he : 1 / (2 : Real) ^ (2 * h) ≤ e) :
    refreshHorizon r n e ≤ 2 ^ (r * n + 2 * h + 4) := by
  have hfrac : 8 * (2 : Real) ^ (r * n) / e ≤
      (2 : Real) ^ (r * n + 2 * h + 3) := by
    calc
      _ ≤ 8 * (2 : Real) ^ (r * n) / (1 / (2 : Real) ^ (2 * h)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) he
      _ = (2 : Real) ^ (r * n + 2 * h + 3) := by
        simp only [div_eq_mul_inv, one_div, inv_inv, pow_add]
        norm_num
        <;> ring
  have hc : Nat.ceil (8 * (2 : Real) ^ (r * n) / e) ≤
      2 ^ (r * n + 2 * h + 3) := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hfrac
  have hp : 1 ≤ 2 ^ (r * n + 2 * h + 3) := by positivity
  unfold refreshHorizon
  rw [show r * n + 2 * h + 4 = (r * n + 2 * h + 3) + 1 by omega, pow_succ]
  omega

/-- The exact finite horizon times the manuscript's per-step union bound is
less than one half. No upper bound on the ambient dimension is assumed. -/
theorem refresh_total_failure_lt_half {h r n : Nat} {e : Real}
    (hh : 16 ≤ h) (hr : 8 * (r + 1) ≤ h)
    (hn : 8 * h + 4 * r + 16 ≤ n)
    (he : 1 / (2 : Real) ^ (2 * h) ≤ e) :
    (refreshHorizon r n e : Real) * refreshFailureBound h r n < 1 / 2 := by
  let E := refreshExponent h r n
  let K := n * (2 * r + 1) + 2 * h + 2 * r + 8
  rcases exponent_guards hh hr hn with ⟨hE4, hxE, hK, hx⟩
  have hEpow : (E : Real) ^ 2 ≤ (2 : Real) ^ E := by
    exact_mod_cast square_le_two_pow hE4
  have hxE' : (h : Real) * (n : Real) ≤ 2 * (E : Real) := by exact_mod_cast hxE
  have hK' : (K : Real) + 1 ≤ 3 * ((h : Real) * (n : Real)) := by
    have hk0 : (n : Real) * (2 * (r : Real) + 1) + 2 * (h : Real) + 2 * (r : Real) + 9 ≤
        3 * ((h : Real) * (n : Real)) := by exact_mod_cast hK
    dsimp [K]
    push_cast
    nlinarith [hk0]
  have hx' : (256 : Real) ≤ (h : Real) * (n : Real) := by exact_mod_cast hx
  have hEsq : ((h : Real) * (n : Real)) ^ 2 ≤ 4 * (E : Real) ^ 2 := by
    have hp := mul_le_mul hxE' hxE' (by positivity : (0 : Real) ≤ (h : Real) * (n : Real))
      (by positivity : (0 : Real) ≤ 2 * (E : Real))
    nlinarith [hp]
  have hdecay : (K : Real) + 1 < (2 : Real) ^ E / 12 := by
    nlinarith [hEpow, hEsq, sq_nonneg ((h : Real) * (n : Real) - 144)]
  have hB : (refreshHorizon r n e : Real) ≤ (2 : Real) ^ (r * n + 2 * h + 4) := by
    exact_mod_cast horizon_le he
  have hrpow : (r : Real) + 1 ≤ (2 : Real) ^ r := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := r)))
  have hD : 16 * ((r : Real) + 1) ^ 2 * (2 : Real) ^ (n * (r + 1)) ≤
      (2 : Real) ^ (n * (r + 1) + 2 * r + 4) := by
    calc
      _ ≤ 16 * ((2 : Real) ^ r) ^ 2 * (2 : Real) ^ (n * (r + 1)) := by gcongr
      _ = (2 : Real) ^ (n * (r + 1) + 2 * r + 4) := by
        rw [show (16 : Real) = 2 ^ (4 : Nat) by norm_num,
          ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
  have hBD : (refreshHorizon r n e : Real) *
      (16 * ((r : Real) + 1) ^ 2 * (2 : Real) ^ (n * (r + 1))) ≤
      (2 : Real) ^ K := by
    calc
      _ ≤ (2 : Real) ^ (r * n + 2 * h + 4) *
          (2 : Real) ^ (n * (r + 1) + 2 * r + 4) :=
        mul_le_mul hB hD (by positivity) (by positivity)
      _ = (2 : Real) ^ K := by rw [← pow_add]; congr 1; dsimp [K]; ring
  have htwoexp : (2 : Real) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : Real)
    linarith
  have hpowexp : (2 : Real) ^ K ≤ Real.exp (K : Real) := by
    calc
      _ ≤ (Real.exp 1) ^ K := by gcongr
      _ = Real.exp (K : Real) := by rw [← Real.exp_nat_mul]; simp
  have hexphalf : Real.exp (-1) < (1 : Real) / 2 := by
    have hquad := Real.quadratic_le_exp_of_nonneg (show (0 : Real) ≤ 1 by norm_num)
    have htwo : (2 : Real) < Real.exp 1 := by norm_num at hquad; linarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact (div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)).2 (by simpa using htwo)
  calc
    (refreshHorizon r n e : Real) * refreshFailureBound h r n =
        ((refreshHorizon r n e : Real) *
        (16 * ((r : Real) + 1) ^ 2 * (2 : Real) ^ (n * (r + 1)))) *
        Real.exp (-((2 : Real) ^ E) / 12) := by dsimp [refreshFailureBound, E]; ring
    _ ≤ Real.exp (K : Real) * Real.exp (-((2 : Real) ^ E) / 12) :=
      mul_le_mul_of_nonneg_right (hBD.trans hpowexp) (by positivity)
    _ = Real.exp ((K : Real) - (2 : Real) ^ E / 12) := by rw [← Real.exp_add]; congr 1; ring
    _ < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
    _ < 1 / 2 := hexphalf

/-- The reciprocal-square threshold retains the required factor of two
after the fresh-label loss, at the original (unchanged) numeric height. -/
theorem refresh_threshold_bounds {m h : Nat} (hm : 256 ≤ m)
    (hh : numericHnum m ≤ h) :
    1 / (2 : Real) ^ (2 * h) ≤ refreshThreshold m h ∧
    2 / (2 : Real) ^ (2 * h) ≤ refreshThreshold m h / 2 := by
  have hg := numeric_robust_dimension_guards hm hh (show 1 ≤ (1 : Nat) by omega)
  have hbsq : (bOf m : Real) ^ 2 ≤ (h : Real) := by exact_mod_cast hg.1
  have hbpos : (0 : Real) < bOf m := by
    have hmpos : 0 < m := by omega
    have : 0 < bOf m := by dsimp [bOf]; positivity
    exact_mod_cast this
  have hrho : 1 ≤ (1 / (bOf m : Real)) ^ 2 * (h : Real) := by
    have hp := mul_le_mul_of_nonneg_left hbsq (sq_nonneg (1 / (bOf m : Real)))
    have hid : (1 / (bOf m : Real)) ^ 2 * (bOf m : Real) ^ 2 = 1 := by
      field_simp [ne_of_gt hbpos]
    rw [hid] at hp
    exact hp
  have he : (2 : Real) - (2 * h : Nat) ≤
      -2 * (1 - 1000 * (1 / (bOf m : Real)) ^ 2) * (h : Real) := by
    push_cast
    nlinarith [hrho]
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) he
  have hid : (2 : Real) ^ ((2 : Real) - (2 * h : Nat)) =
      4 / (2 : Real) ^ (2 * h) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num [Real.rpow_natCast, div_eq_mul_inv]
  rw [hid] at hpow
  change 4 / (2 : Real) ^ (2 * h) ≤ refreshThreshold m h at hpow
  constructor <;> nlinarith [show 0 < 1 / (2 : Real) ^ (2 * h) by positivity]

/-- The exact manuscript B_n F_n inequality uses the same numeric selector
parameters; it introduces no additional source-size floor. -/
theorem numeric_refresh_total_failure_lt_half {m h A : Nat}
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h) (hA : 1 ≤ A) :
    (refreshHorizon (numericRankThreshold m) (2 * blocks A h) (refreshThreshold m h) : Real) *
      refreshFailureBound h (numericRankThreshold m) (2 * blocks A h) < 1 / 2 := by
  have hg := numeric_robust_dimension_guards hm hh hA
  exact refresh_total_failure_lt_half hg.2.2.1 hg.2.1 hg.2.2.2.2.1
    (refresh_threshold_bounds hm hh).1

/-- The natural exponent used in the finite formula equals the signed Real
exponent in the manuscript; neither subtraction was truncated. -/
theorem refreshExponent_cast_eq {h r n : Nat}
    (hh : 16 ≤ h) (hr : 8 * (r + 1) ≤ h)
    (hn : 8 * h + 4 * r + 16 ≤ n) :
    (refreshExponent h r n : Real) =
      (2 * (h : Real) - r) * ((n : Real) - r - 2 * h) + 2 - 4 * h := by
  have hu : h ≤ 2 * h - r := by omega
  have hv : 16 ≤ n - r - 2 * h := by omega
  have hp : 4 * h ≤ (2 * h - r) * (n - r - 2 * h) + 2 := by
    nlinarith [Nat.mul_le_mul hu hv]
  have hur : r ≤ 2 * h := by omega
  have hnr : r ≤ n := by omega
  have hnv : 2 * h ≤ n - r := by omega
  simp only [refreshExponent, Nat.cast_sub hp, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hur, Nat.cast_sub hnv, Nat.cast_sub hnr, Nat.cast_ofNat]

/-- Subtracting the all-Q nontransversality loss preserves the exact target
probability. The input mass is the unconditioned complement/advice lower
bound; it is never renormalized on successful complements. -/
theorem all_advice_probability_lower {m h r n a : Nat} {S : Real}
    (hm : 1 ≤ m) (hh : 1 ≤ h) (ha : a ≤ r)
    (hquad : 4 * m * h + m + 3 * (r + 1) + 1 ≤ h ^ 2)
    (hn : 5 * h ^ 2 + r + 2 ≤ n)
    (hS : 1 / (2 : Real) ^ (2 * m * h) ≤ S) :
    1 / (2 : Real) ^ (6 * h ^ 2) ≤
      2 * S ^ 2 / ((2 : Real) ^ (4 * h ^ 2) * (m : Real) * ((r : Real) + 1) ^ 3) -
        (2 : Real) ^ (a + 1) / (2 : Real) ^ n := by
  let D : Real := (2 : Real) ^ (4 * h ^ 2) * (m : Real) * ((r : Real) + 1) ^ 3
  have hmpos : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hmPow : (m : Real) ≤ (2 : Real) ^ m := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have hrPow : (r : Real) + 1 ≤ (2 : Real) ^ (r + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := r + 1)).le
  have hpoly : (m : Real) * ((r : Real) + 1) ^ 3 ≤
      (2 : Real) ^ (m + 3 * (r + 1)) := by
    calc
      _ ≤ (2 : Real) ^ m * ((2 : Real) ^ (r + 1)) ^ 3 := by gcongr
      _ = (2 : Real) ^ (m + 3 * (r + 1)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have hden : (2 : Real) ^ (4 * m * h) * D ≤ (2 : Real) ^ (5 * h ^ 2) := by
    calc
      _ = (2 : Real) ^ (4 * m * h + 4 * h ^ 2) *
          ((m : Real) * ((r : Real) + 1) ^ 3) := by dsimp [D]; rw [pow_add]; ring
      _ ≤ (2 : Real) ^ (4 * m * h + 4 * h ^ 2) *
          (2 : Real) ^ (m + 3 * (r + 1)) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = (2 : Real) ^ (4 * m * h + 4 * h ^ 2 + (m + 3 * (r + 1))) := by rw [pow_add]
      _ ≤ (2 : Real) ^ (5 * h ^ 2) := by gcongr; omega
  have hden' : ((2 : Real) ^ (2 * m * h)) ^ 2 * D ≤ (2 : Real) ^ (5 * h ^ 2) := by
    calc
      _ = (2 : Real) ^ (4 * m * h) * D := by rw [← pow_mul]; congr 2; ring
      _ ≤ _ := hden
  have hmass : 1 / (2 : Real) ^ (5 * h ^ 2) ≤ 2 * S ^ 2 / D := by
    calc
      _ ≤ 1 / (((2 : Real) ^ (2 * m * h)) ^ 2 * D) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden'
      _ = (1 / (2 : Real) ^ (2 * m * h)) ^ 2 / D := by field_simp; ring
      _ ≤ S ^ 2 / D := by gcongr
      _ ≤ 2 * S ^ 2 / D :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg S]) hDpos.le
  have hdim : (a + 1) + (5 * h ^ 2 + 1) ≤ n := by omega
  have hloss : (2 : Real) ^ (a + 1) / (2 : Real) ^ n ≤
      1 / (2 : Real) ^ (5 * h ^ 2 + 1) := by
    calc
      _ ≤ (2 : Real) ^ (a + 1) / (2 : Real) ^ ((a + 1) + (5 * h ^ 2 + 1)) := by
        gcongr
      _ = 1 / (2 : Real) ^ (5 * h ^ 2 + 1) := by rw [pow_add]; field_simp
  have hhalf : 1 / (2 : Real) ^ (5 * h ^ 2) -
      1 / (2 : Real) ^ (5 * h ^ 2 + 1) = 1 / (2 : Real) ^ (5 * h ^ 2 + 1) := by
    rw [pow_succ]
    field_simp
    <;> ring
  have htarget : 1 / (2 : Real) ^ (6 * h ^ 2) ≤
      1 / (2 : Real) ^ (5 * h ^ 2 + 1) := by
    have hh2 : 1 ≤ h ^ 2 := Nat.one_le_pow 2 h hh
    gcongr
    omega
  change 1 / (2 : Real) ^ (6 * h ^ 2) ≤ 2 * S ^ 2 / D - _
  linarith [hmass, hloss, hhalf, htarget]

/-- The unconditioned advice correction follows from the same numeric floor
and the exact rational `successMargin` already used by the inverse theorem. -/
theorem numeric_all_advice_probability_lower {m h A a : Nat}
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h) (hA : 1 ≤ A)
    (ha : a ≤ numericRankThreshold m) :
    let S : Real := ((ActualStarAcceptedGoodMass.successMargin
      (ActualStarFixedRhoDimensionGuard.badExponent m h) : Rat) : Real)
    1 / (2 : Real) ^ (6 * h ^ 2) ≤
      2 * S ^ 2 / ((2 : Real) ^ (4 * h ^ 2) * (m : Real) *
        ((numericRankThreshold m : Real) + 1) ^ 3) -
        (2 : Real) ^ (a + 1) / (2 : Real) ^ (2 * blocks A h) := by
  have hg := numeric_robust_dimension_guards hm hh hA
  have hE : ActualStarFixedRhoDimensionGuard.badExponent m h ≤ 2 * m * h := by
    unfold ActualStarFixedRhoDimensionGuard.badExponent
    exact Nat.mul_le_mul_left (2 * m) (Nat.sub_le _ _)
  have hS : 1 / (2 : Real) ^ (2 * m * h) ≤
      ((ActualStarAcceptedGoodMass.successMargin
        (ActualStarFixedRhoDimensionGuard.badExponent m h) : Rat) : Real) := by
    have hcast : ((ActualStarAcceptedGoodMass.successMargin
        (ActualStarFixedRhoDimensionGuard.badExponent m h) : Rat) : Real) =
        1 / (2 : Real) ^ (ActualStarFixedRhoDimensionGuard.badExponent m h) := by
      simp [ActualStarAcceptedGoodMass.successMargin]
    rw [hcast]
    gcongr
  exact all_advice_probability_lower (by omega) (by have := hg.2.2.1; omega)
    ha hg.2.2.2.2.2.2 hg.2.2.2.2.2.1 hS

end
end PvNP.RealizableHardness.ActualNumericRobustReal
