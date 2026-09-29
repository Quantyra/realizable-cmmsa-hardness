import PvNP.RealizableHardness.ActualTheorem1
import PvNP.RealizableHardness.ActualModifiedPcpParameterOrder
import PvNP.RealizableHardness.ActualCertifiedManuscriptParameters
import Mathlib.Tactic

/-!
Conditional arithmetic and reduction assembly for manuscript Theorem 1.

External inputs are theorem parameters below, never Lean axioms.  The MZ
outer-hardness contract is manuscript Section 3, MZ Theorem 3.1/Claim 3.2.
The changed-ambient 8S decoder application, star NO reduction, finite-list
repair, and encoded FP implementation are **new obligations**, not imported
MZ/HN contracts.  In particular, no field here asserts the whole
source-to-CMMSA reduction as a cited result.

The arithmetic below formalizes manuscript equations (19)--(21) with the
factor two from conditioning and with the outer YES error chosen *after*
`m`, `h`, and `J` for each positive target completeness error.
-/

namespace PvNP.RealizableHardness.ActualConditionalTheorem1Core

open Complexity RandomizedReduction
open ActualCMMSARandomizedReduction
open ActualModifiedPcpParameterOrder
open ActualCertifiedManuscriptParameters

set_option autoImplicit false

/-- The manuscript's late outer YES error, equation (20). -/
def outerYesError (m J : Nat) (τ : Rat) : Rat :=
  τ / (100 * ((m + 1 : Nat) : Rat) * (J : Rat))

theorem outerYesError_pos {m J : Nat} {τ : Rat}
    (hJ : 0 < J) (hτ : 0 < τ) :
    0 < outerYesError m J τ := by
  unfold outerYesError
  positivity

/-- Equation (21): conditioning on legitimate tuples with bad mass at most
`1/4` costs at most `4/3`, and all `m+1` blocks remain below `τ/75`. -/
theorem conditioned_honest_failure_lt {m J : Nat} {τ ε₁ a : Rat}
    (hJ : 0 < J) (hτ : 0 < τ)
    (ha : a ≤ 1 / 4)
    (hε : ε₁ ≤ outerYesError m J τ) :
    ((m + 1 : Nat) : Rat) * (J : Rat) * ε₁ / (1 - a) ≤ τ / 75 := by
  have hJq : (0 : Rat) < J := by exact_mod_cast hJ
  have hm : (0 : Rat) < ((m + 1 : Nat) : Rat) := by exact_mod_cast Nat.succ_pos m
  have hden : (0 : Rat) < 1 - a := by linarith
  have hdenlb : (3 / 4 : Rat) ≤ 1 - a := by linarith
  have hbase : ((m + 1 : Nat) : Rat) * (J : Rat) * ε₁ ≤ τ / 100 := by
    have h := mul_le_mul_of_nonneg_left hε (mul_nonneg hm.le hJq.le)
    unfold outerYesError at h
    field_simp at h ⊢
    nlinarith
  apply (div_le_div_iff₀ hden (by norm_num : (0 : Rat) < 75)).2
  have hmul : ((m + 1 : Nat) : Rat) * (J : Rat) * ε₁ * 75 ≤ (τ / 100) * 75 :=
    mul_le_mul_of_nonneg_right hbase (by norm_num)
  nlinarith

/-- The positive **real** outer soundness constant permits choosing integer
`A` after `κ` and before `h`, as manuscript equation (19) requires. -/
theorem exists_outer_repetition_scale (κ : Real) (hκ : 0 < κ) :
    ∃ A : Nat, 20 < κ * (A : Real) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (20 / κ)
  refine ⟨A, ?_⟩
  have hA' : 20 / κ < (A : Real) := hA
  have hκne : κ ≠ 0 := ne_of_gt hκ
  apply (div_lt_iff₀ hκ).mp at hA'
  nlinarith

/-- The factor-two conditioned outer bound is strictly below decoded success
`2^(-10h²)` for a positive real `κ` and `20<κA`. This is the numerical NO
contradiction in manuscript equation (19), without an integral-κ assumption. -/
theorem conditioned_outer_lt_decoded
    (κ : Real) (A h : Nat) (hA : 20 < κ * (A : Real)) (hh : 0 < h) :
    2 * ((1 / 2 : Real) ^ (κ * (A : Real) * (h : Real) ^ 2)) <
      ((1 / 2 : Real) ^ (10 * (h : Real) ^ 2)) := by
  have hsq : (1 : Real) ≤ (h : Real) ^ 2 := by
    have hh' : (1 : Real) ≤ h := by exact_mod_cast hh
    nlinarith
  have hExp : 10 * (h : Real) ^ 2 + 1 < κ * (A : Real) * (h : Real) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hA) (by positivity : (0 : Real) < (h : Real) ^ 2)]
  have hbase0 : (0 : Real) < 1 / 2 := by norm_num
  have hbase1 : (1 / 2 : Real) < 1 := by norm_num
  have hlt := Real.rpow_lt_rpow_of_exponent_gt hbase0 hbase1 hExp
  have heq :
      2 * ((1 / 2 : Real) ^ (10 * (h : Real) ^ 2 + 1)) =
        ((1 / 2 : Real) ^ (10 * (h : Real) ^ 2)) := by
    rw [Real.rpow_add_one (by norm_num : (1 / 2 : Real) ≠ 0)]
    ring
  calc
    2 * ((1 / 2 : Real) ^ (κ * (A : Real) * (h : Real) ^ 2)) <
        2 * ((1 / 2 : Real) ^ (10 * (h : Real) ^ 2 + 1)) :=
      mul_lt_mul_of_pos_left hlt (by norm_num)
    _ = ((1 / 2 : Real) ^ (10 * (h : Real) ^ 2)) := heq

/-- The conditional NO contradiction after a changed-ambient decoder has
produced a strategy. The existence of that strategy is a manuscript-new
obligation, rather than a field of the cited MZ decoder contract. -/
theorem no_strategy_from_outer_and_changed_ambient
    (κ : Real) (A h : Nat) (hA : 20 < κ * (A : Real)) (hh : 0 < h)
    (success : Real)
    (hnewDecoder : ((1 / 2 : Real) ^ (10 * (h : Real) ^ 2)) ≤ success)
    (hExternalOuter : success ≤
      2 * ((1 / 2 : Real) ^ (κ * (A : Real) * (h : Real) ^ 2))) : False := by
  have hstrict := conditioned_outer_lt_decoded κ A h hA hh
  exact (not_lt_of_ge hnewDecoder) (lt_of_le_of_lt hExternalOuter hstrict)

end PvNP.RealizableHardness.ActualConditionalTheorem1Core
