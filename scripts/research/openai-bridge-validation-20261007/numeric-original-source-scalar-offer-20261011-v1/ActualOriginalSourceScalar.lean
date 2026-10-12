import PvNP.RealizableHardness.ActualCountedAssignmentScore
import PvNP.RealizableHardness.ActualMaximalCountSpecialization

/-! Exact count-cost absorption and the strict imported outer exponent
comparison. This scalar module does not instantiate a source-game bound.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualOriginalSourceScalar

open ActualCountedAssignmentScore ActualMaximalCountSpecialization
open ActualNumericSourceHeight ActualCmmsaParameterReconciliation SamplerParameters
open DropTailParameters

set_option autoImplicit false
noncomputable section

/-- The one eligibility factor, count factor, level choice and ambient
extension cost are exactly the captured combined denominator. -/
theorem counted_cost_product_eq {m h : Nat} (hm : 1 ≤ m) :
    (1 : Real) / 2 * (countedAssignmentCost m h * decay 8 h) =
      decay 8 h / ((combinedCountCost m : Real) * (2 : Real) ^ (countExponent m * h)) := by
  have hmpos : 0 < m := by omega
  have hc : 0 < countConstant m := by
    unfold countConstant countReciprocal bOf
    positivity
  have hcr : (0 : Real) < countConstant m := by exact_mod_cast hc
  have hr : (0 : Real) < (numericRankThreshold m : Real) + 1 := by positivity
  unfold countedAssignmentCost combinedCountCost
  push_cast
  field_simp [ne_of_gt hcr, ne_of_gt hr]
  <;> ring

theorem decay9_le_counted_cost {m h : Nat} (hm : 1 ≤ m)
    (hh : countCostHeight m ≤ h) :
    decay 9 h ≤ (1 : Real) / 2 * (countedAssignmentCost m h * decay 8 h) := by
  rw [counted_cost_product_eq hm]
  exact count_cost_retains_decay9 hm hh

/-- Reciprocal notation for the declared q=2 source-game exponential bound.
The constant and fixed source gap remain explicit external parameters. -/
def sourceOuterUpper (kappa gap : Real) (A r h : Nat) : Real :=
  1 / (2 : Real) ^ ((kappa * gap ^ 2 * (A : Real) / (2 : Real) ^ r) * (h : Real) ^ 2)

/-- Substitution of the actual beta and number of repeated equations is
an exact identity, before applying the external source theorem. -/
theorem original_outer_exponent_identity (kappa gap : Real) (A r h : Nat) :
    (kappa * gap ^ 2 / (2 : Real) ^ r) * (beta A h : Real) * (blocks A h : Real) =
      (kappa * gap ^ 2 * (A : Real) / (2 : Real) ^ r) * (h : Real) ^ 2 := by
  have hJ : (0 : Real) < blocks A h := by unfold blocks; positivity
  unfold beta
  push_cast
  field_simp [ne_of_gt hJ]
  <;> ring

/-- A strict fixed coefficient inequality, with positive height, supplies
the strict soundness comparison needed by the contradiction. -/
theorem source_outer_upper_lt_decay9 {kappa gap : Real} {A r h : Nat}
    (hcoef : 9 < kappa * gap ^ 2 * (A : Real) / (2 : Real) ^ r)
    (hh : 0 < h) : sourceOuterUpper kappa gap A r h < decay 9 h := by
  have hhreal : (0 : Real) < h := by exact_mod_cast hh
  have hhsq : (0 : Real) < (h : Real) ^ 2 := by positivity
  have hpow : (2 : Real) ^ (9 * h ^ 2) <
      (2 : Real) ^ ((kappa * gap ^ 2 * (A : Real) / (2 : Real) ^ r) * (h : Real) ^ 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    push_cast
    exact mul_lt_mul_of_pos_right hcoef hhsq
  unfold sourceOuterUpper
  rw [decay_eq_reciprocal]
  exact one_div_lt_one_div_of_lt (by positivity) hpow

/-- Scalar end of the argument only: the actual strategy must separately
supply both inequalities, and the imported bound must be applicable. -/
theorem source_scalar_contradiction {m h A : Nat} {kappa gap score : Real}
    (hm : 1 ≤ m) (hcost : countCostHeight m ≤ h) (hh : 0 < h)
    (hcoef : 9 < kappa * gap ^ 2 * (A : Real) / (2 : Real) ^ numericRankThreshold m)
    (hlower : (1 : Real) / 2 * (countedAssignmentCost m h * decay 8 h) ≤ score)
    (hupper : score ≤ sourceOuterUpper kappa gap A (numericRankThreshold m) h) : False := by
  have hlo := (decay9_le_counted_cost hm hcost).trans hlower
  have hhi := hupper.trans_lt (source_outer_upper_lt_decay9 hcoef hh)
  exact (not_lt_of_ge hlo) hhi

end
end PvNP.RealizableHardness.ActualOriginalSourceScalar
