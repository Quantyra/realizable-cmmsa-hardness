import PvNP.RealizableHardness.ActualNumericExplicitHeight
import PvNP.RealizableHardness.ActualNumericSourceHeight
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.SamplerParameters
import Mathlib.Tactic

/-! Explicit robust-local arithmetic supplied by the existing numeric floor.
Uncompiled candidate: no refresh law, history, or decoder is asserted here. -/

namespace PvNP.RealizableHardness.ActualNumericRobustCutoffs

open ActualNumericExplicitHeight ActualNumericSourceHeight
open ActualCmmsaParameterReconciliation ActualCmmsaAdmissibilitySelector
open SamplerParameters

set_option autoImplicit false
noncomputable section

def RobustDimensionGuards (m h A : Nat) : Prop :=
  let r := numericRankThreshold m
  bOf m ^ 2 ≤ h ∧ 8 * (r + 1) ≤ h ∧ 16 ≤ h ∧
    8 * h ^ 2 ≤ 2 * blocks A h ∧
    8 * h + 4 * r + 16 ≤ 2 * blocks A h ∧
    5 * h ^ 2 + r + 2 ≤ 2 * blocks A h ∧
    4 * m * h + m + 3 * (r + 1) + 1 ≤ h ^ 2

private theorem two_pow_ge_add_two {q : Nat} (hq : 2 ≤ q) : q + 2 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      rw [pow_succ]
      omega

/-- The existing numeric height, without an increased source floor, supplies
the dimensional, threshold and distinct-advice arithmetic for robust-local. -/
theorem numeric_robust_dimension_guards {m h A : Nat}
    (hm : 256 ≤ m) (hh : numericHnum m ≤ h) (hA : 1 ≤ A) :
    RobustDimensionGuards m h A := by
  let b := bOf m
  let r := numericRankThreshold m
  have hm1 : 1 ≤ m := by omega
  have hb : 4000 ≤ b := by
    dsimp [b, bOf]
    nlinarith [Nat.one_le_pow 2 m hm1]
  have hr : r = 10 * m * b := rfl
  have hmr : m ≤ r := by
    rw [hr]
    nlinarith [Nat.mul_le_mul_left m hb]
  have hfinal : numericHfinal m ≤ numericHnum m :=
    (Nat.le_max_right (numericRankThreshold m + 7) (numericHfinal m)).trans
      (Nat.le_max_right (numericRankThreshold m)
        (max (numericRankThreshold m + 7) (numericHfinal m)))
  have hH : 2 * b * (numericN m + 2) ≤ h := hfinal.trans hh
  have hN : m * (r + 1) ≤ numericN m + 2 := by
    dsimp [numericN, r]
    omega
  have hcore : 2 * b * (m * (r + 1)) ≤ h :=
    (Nat.mul_le_mul_left (2 * b) hN).trans hH
  have hbr : b ≤ r := by
    rw [hr]
    nlinarith [Nat.mul_le_mul_right b hm1]
  have hbmul : b ≤ 2 * b * m := by
    nlinarith [Nat.mul_le_mul_left b hm1]
  have hbsq : b ^ 2 ≤ h := by
    calc
      b ^ 2 = b * b := by ring
      _ ≤ (2 * b * m) * r := Nat.mul_le_mul hbmul hbr
      _ ≤ 2 * b * (m * (r + 1)) := by nlinarith
      _ ≤ h := hcore
  have hcoef : 8 ≤ 2 * b * m := by
    nlinarith [Nat.mul_le_mul hb hm1]
  have h8r : 8 * (r + 1) ≤ h := by
    have hp := Nat.mul_le_mul_right (r + 1) hcoef
    nlinarith [hp, hcore]
  have h8m : 8 * m ≤ h := by omega
  have h16 : 16 ≤ h := by omega
  have hrh : r ≤ h := by omega
  have h16sq : 16 * h ≤ h ^ 2 := by
    nlinarith [Nat.mul_le_mul_left h h16]
  have hq : 2 ≤ A * h ^ 2 := by
    have hp := Nat.mul_le_mul_right (h ^ 2) hA
    nlinarith [hp]
  have hinner : h ^ 2 + 2 ≤ 2 ^ (A * h ^ 2) :=
    (Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right (h ^ 2) hA) 2).trans
      (two_pow_ge_add_two hq)
  have hpow : 2 ^ (h ^ 2 + 2) ≤ 2 ^ (2 ^ (A * h ^ 2)) :=
    Nat.pow_le_pow_right (by norm_num) hinner
  have hblocks : 4 * h ^ 2 ≤ blocks A h := by
    calc
      4 * h ^ 2 ≤ 4 * 2 ^ (h ^ 2) :=
        Nat.mul_le_mul_left 4 (le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ (h ^ 2 + 2) := by rw [pow_add]; norm_num <;> ring
      _ ≤ blocks A h := hpow
  have hn : 8 * h ^ 2 ≤ 2 * blocks A h := by
    nlinarith [Nat.mul_le_mul_left 2 hblocks]
  have hdim : 8 * h + 4 * r + 16 ≤ 2 * blocks A h := by
    nlinarith [hn]
  have hcorrection : 5 * h ^ 2 + r + 2 ≤ 2 * blocks A h := by
    nlinarith [hn]
  have hlarge : 8 * m * h ≤ h ^ 2 := by
    nlinarith [Nat.mul_le_mul_right h h8m]
  have hsmall : 2 * (m + 3 * (r + 1) + 1) ≤ h := by omega
  have hquad : 4 * m * h + m + 3 * (r + 1) + 1 ≤ h ^ 2 := by
    nlinarith [hlarge, hsmall]
  exact ⟨hbsq, h8r, h16, hn, hdim, hcorrection, hquad⟩

/-- Every output of the same numeric selector inherits the robust arithmetic;
no independent height choice or additional selector premise is introduced. -/
theorem selected_robust_dimension_guards
    (base : Nat → Nat) (cutoff : Real → Nat) {L m A : Nat}
    (hA : 1 ≤ A)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat)) :
    RobustDimensionGuards m (hBlock L m) A := by
  have hheight := selected_numeric_height (numericBase base) cutoff
    (by simpa only [numericSourceBase_eq, numericSourceFloor] using hsel)
  rcases hheight with ⟨hm, _, hbase, _, _⟩
  exact numeric_robust_dimension_guards hm
    ((Nat.le_max_right (base m) (numericHnum m)).trans hbase) hA

end
end PvNP.RealizableHardness.ActualNumericRobustCutoffs
