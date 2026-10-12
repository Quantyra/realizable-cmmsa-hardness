import PvNP.RealizableHardness.ActualMaximalCountGuards
import PvNP.RealizableHardness.ActualNumericRobustReal
import PvNP.RealizableHardness.ActualVisibleListStrategy
import PvNP.RealizableHardness.DropTailParameters
import Mathlib.Tactic

/-! Specialize the declared external all-window count to fixed-index natural
constants. The external count remains an explicit hypothesis, not a new axiom
or a locally proved counting theorem. Uncompiled and unaccepted candidate. -/
namespace PvNP.RealizableHardness.ActualMaximalCountSpecialization

open ActualCmmsaParameterReconciliation ActualNumericSourceHeight
open ActualNumericExplicitHeight ActualNumericRobustReal
open ActualVisibleListStrategy ActualMaximalPairLadder GrassmannCounting
open DropTailParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The reciprocal of delta=rho/m at the actual rho=1/bOf(m). -/
def countReciprocal (m : Nat) : Nat := bOf m * m

/-- The factorial parameter is exactly integral for these reciprocal inputs. -/
def countSourceT (m : Nat) : Nat :=
  Nat.factorial (2 ^ (2 + 1000 * countReciprocal m ^ 5))

def countLinearExponent (m : Nat) : Nat :=
  100 * Nat.factorial (countSourceT m - 1) * (10 * countReciprocal m) ^ 2 *
    countReciprocal m ^ 5

def countConstant (m : Nat) : Nat :=
  160 * countReciprocal m * (20 * 5 ^ numericRankThreshold m) ^ 2

def countExponent (m : Nat) : Nat := countLinearExponent m + 4

/-- Includes list size, fixed level, extension, and the conservative row factor. -/
def combinedCountCost (m : Nat) : Nat :=
  2 * countConstant m * (numericRankThreshold m + 1) * 2 ^ numericRankThreshold m

def countCostHeight (m : Nat) : Nat := countExponent m + combinedCountCost m

/-- The source's reciprocal parameters have exact integer identities.
The second identity fixes the natural exponent inside its factorial t. -/
theorem reciprocal_source_parameters {m : Nat} (hm : 1 ≤ m) :
    (1 / (bOf m : Real)) / (m : Real) = 1 / (countReciprocal m : Real) ∧
    10 / (((1 / (countReciprocal m : Real)) ^ 5) / 100) =
      ((1000 * countReciprocal m ^ 5 : Nat) : Real) ∧
    (10 : Real) / (1 / (countReciprocal m : Real)) =
      (numericRankThreshold m : Real) := by
  have hmpos : 0 < m := by omega
  have hbpos : 0 < bOf m := by unfold bOf; positivity
  have hnpos : 0 < countReciprocal m := Nat.mul_pos hbpos hmpos
  have hn : (countReciprocal m : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  refine ⟨?_, ?_, ?_⟩
  · simp only [countReciprocal, Nat.cast_mul, one_div, div_eq_mul_inv, mul_inv_rev]
    ring
  · push_cast
    field_simp [hn]
    <;> ring
  · simp only [one_div, div_eq_mul_inv, inv_inv, numericRankThreshold,
      countReciprocal, Nat.cast_mul, Nat.cast_ofNat]
    ring

/-- Convert the exact external count at one actual ladder level into constants
depending only on the fixed index. Its source-height, dimension, advice, and
threshold applicability are separately supplied by the declared import. -/
theorem actual_level_count_of_declared_contract
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {a m h j : Nat}
    (T : (L : Grass V (2 * h)) → Module.Dual (ZMod 2) L.val)
    (Q : Grass V a) (C : Rat) (hC : 0 < C)
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h)
    (hj : j ≤ numericRankThreshold m)
    (hthreshold : refreshThreshold m h / 5 < (C : Real))
    (hImported :
      ((maximalPairList T Q (numericRankThreshold m) (C / (4 * 5 ^ j))).card : Real) ≤
        (160 * (countReciprocal m : Real)) /
          (((C / (4 * 5 ^ j) : Rat) : Real) ^ 2) *
            (2 : Real) ^ (countLinearExponent m * h)) :
    ((maximalPairList T Q (numericRankThreshold m) (C / (4 * 5 ^ j))).card : Real) ≤
      (countConstant m : Real) * (2 : Real) ^ (countExponent m * h) := by
  let r := numericRankThreshold m
  let B : Real := (C / (4 * 5 ^ j) : Rat)
  let D : Real := 20 * (5 : Real) ^ r
  have hBpos : 0 < B := by dsimp [B]; exact_mod_cast (div_pos hC (by positivity))
  have hDpos : 0 < D := by dsimp [D]; positivity
  have he := (refresh_threshold_bounds hm hh).1
  have hClinear : (1 / (2 : Real) ^ (2 * h)) / 5 < (C : Real) :=
    (div_le_div_of_nonneg_right he (by norm_num)).trans_lt hthreshold
  have hlevel : (4 : Real) * 5 ^ j ≤ 4 * 5 ^ r :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (by norm_num)
  have hBj : (1 / (2 : Real) ^ (2 * h)) / D ≤ B := by
    calc
      _ = ((1 / (2 : Real) ^ (2 * h)) / 5) / (4 * 5 ^ r) := by
        dsimp [D]
        field_simp <;> ring
      _ ≤ ((1 / (2 : Real) ^ (2 * h)) / 5) / (4 * 5 ^ j) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlevel
      _ ≤ (C : Real) / (4 * (5 : Real) ^ j) :=
        (div_lt_div_of_pos_right hClinear (by positivity)).le
      _ = B := by dsimp [B]; push_cast; rfl
  have hInv : 1 / B ≤ D * (2 : Real) ^ (2 * h) := by
    calc
      1 / B ≤ 1 / ((1 / (2 : Real) ^ (2 * h)) / D) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hBj
      _ = D * (2 : Real) ^ (2 * h) := by field_simp [ne_of_gt hDpos] <;> ring
  have hpow : ((2 : Real) ^ (2 * h)) ^ 2 = (2 : Real) ^ (4 * h) := by
    rw [← pow_mul]
    congr 1
    ring
  have hInvSq : 1 / B ^ 2 ≤ D ^ 2 * (2 : Real) ^ (4 * h) := by
    calc
      1 / B ^ 2 = (1 / B) ^ 2 := by field_simp [ne_of_gt hBpos] <;> ring
      _ ≤ (D * (2 : Real) ^ (2 * h)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hInv 2
      _ = D ^ 2 * (2 : Real) ^ (4 * h) := by rw [mul_pow, hpow]
  calc
    _ ≤ (160 * (countReciprocal m : Real)) / B ^ 2 *
        (2 : Real) ^ (countLinearExponent m * h) := hImported
    _ ≤ (160 * (countReciprocal m : Real)) *
        (D ^ 2 * (2 : Real) ^ (4 * h)) *
          (2 : Real) ^ (countLinearExponent m * h) := by
      have hs := mul_le_mul_of_nonneg_left hInvSq
        (show (0 : Real) ≤ 160 * (countReciprocal m : Real) by positivity)
      have hp := mul_le_mul_of_nonneg_right hs
        (show (0 : Real) ≤ (2 : Real) ^ (countLinearExponent m * h) by positivity)
      simpa only [div_eq_mul_inv, one_div] using hp
    _ = (countConstant m : Real) * (2 : Real) ^ (countExponent m * h) := by
      simp only [countConstant, countExponent, Nat.add_mul, pow_add,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, D, r]
      ring

/-- This denominator is strictly positive at every actual positive index. -/
theorem combinedCountCost_pos {m : Nat} (hm : 1 ≤ m) : 0 < combinedCountCost m := by
  have hmpos : 0 < m := by omega
  have hbpos : 0 < bOf m := by unfold bOf; positivity
  unfold combinedCountCost countConstant countReciprocal
  positivity

/-- A conservative natural same-index floor pays all fixed count/strategy
costs with one quadratic dyadic exponent. No effective external cutoff is inferred. -/
theorem combined_count_cost_le_dyadic {m h : Nat}
    (hm : 1 ≤ m) (hh : countCostHeight m ≤ h) :
    combinedCountCost m * 2 ^ (countExponent m * h) ≤ 2 ^ (h ^ 2) := by
  let K := combinedCountCost m
  let B := countExponent m
  have hKpos : 0 < K := combinedCountCost_pos hm
  have hfloor : B + K ≤ h := hh
  have hh1 : 1 ≤ h := by omega
  have hK : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
  have hexp : K + B * h ≤ h ^ 2 := by
    have hmul := Nat.mul_le_mul_right h hfloor
    have hKh : K ≤ K * h := by simpa using Nat.mul_le_mul_left K hh1
    nlinarith
  calc
    K * 2 ^ (B * h) ≤ 2 ^ K * 2 ^ (B * h) := Nat.mul_le_mul_right _ hK
    _ = 2 ^ (K + B * h) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (h ^ 2) := pow_le_pow_right₀ (by omega) hexp

/-- The D8 actual event bound retains D9 after the explicit count, extension,
level, and row denominator. The game-probability identification remains separate. -/
theorem count_cost_retains_decay9 {m h : Nat}
    (hm : 1 ≤ m) (hh : countCostHeight m ≤ h) :
    decay 9 h ≤ decay 8 h /
      ((combinedCountCost m : Real) * (2 : Real) ^ (countExponent m * h)) := by
  have hKpos : (0 : Real) < combinedCountCost m := by
    exact_mod_cast combinedCountCost_pos hm
  have hcost : (combinedCountCost m : Real) * (2 : Real) ^ (countExponent m * h) ≤
      (2 : Real) ^ (h ^ 2) := by
    exact_mod_cast combined_count_cost_le_dyadic hm hh
  have hinv : 1 / (2 : Real) ^ (h ^ 2) ≤
      1 / ((combinedCountCost m : Real) * (2 : Real) ^ (countExponent m * h)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcost
  have hprod := mul_le_mul_of_nonneg_left hinv (decay_pos 8 h).le
  have hdecay : decay 9 h = decay 8 h * (1 / (2 : Real) ^ (h ^ 2)) := by
    calc
      decay 9 h = decay 8 h * decay 1 h := by simpa using decay_add 8 1 h
      _ = decay 8 h * (1 / (2 : Real) ^ (h ^ 2)) := by
        rw [decay_eq_reciprocal 1 h]
        simp
  rw [hdecay]
  simpa only [div_eq_mul_inv, one_div] using hprod

end
end PvNP.RealizableHardness.ActualMaximalCountSpecialization
