import PvNP.RealizableHardness.ActualOccurrenceGapBridge
import PvNP.RealizableHardness.BooleanParityInput
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Literal list-indexed Boolean parity to the actual occurrence allocation.
This CMMSA candidate imports the shared literal Boolean input interface; it
does not certify the upstream reduction across toolchains. -/
namespace PvNP.RealizableHardness.ActualBooleanOccurrenceSource

open scoped BigOperators
open ActualOccurrenceAllocation ActualOccurrenceGapBridge ActualOriginalSourceNo BooleanParityInput

set_option autoImplicit false
noncomputable section

def asInstance (I : BooleanParityInput.Input) : Instance I.variables I.equations.length where
  vars r := ![(I.equations.get r).first, (I.equations.get r).second,
    (I.equations.get r).third]
  rhs r := valueOf (I.equations.get r).rhs

theorem rows_positive (I : BooleanParityInput.Input) : 0 < I.equations.length :=
  List.length_pos_iff.mpr I.nonempty

/-- Both sides use the same ordered three slots, even for repeated owners. -/
theorem parity_iff (a b c d : Bool) :
    ((xor (xor a b) c) == d) = true ↔ valueOf a + valueOf b + valueOf c = valueOf d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [valueOf]

private theorem countP_as_sum {V : Type*} (p : V → Bool) (l : List V) :
    l.countP p = (l.map (fun v => if p v then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons v l ih => cases h : p v <;> simp [h, ih, Nat.add_comm]

/-- List positions, rather than the set of distinct equations, index the sum. -/
theorem failureCount_index_sum (I : BooleanParityInput.Input) (a : Fin I.variables → Bool) :
    BooleanParityInput.failureCount I a = ∑ r : Fin I.equations.length,
      if BooleanParityInput.satisfied (I.equations.get r) a then 0 else 1 := by
  unfold BooleanParityInput.failureCount
  calc
    I.equations.countP (fun e => !(satisfied e a)) =
        (List.ofFn I.equations.get).countP (fun e => !(satisfied e a)) := by
      rw [List.ofFn_get]
    _ = _ := by
      rw [countP_as_sum, List.map_ofFn, Fin.sum_ofFn]
      apply Finset.sum_congr rfl
      intro r _
      cases BooleanParityInput.satisfied (I.equations.get r) a <;> rfl

theorem raw_violations_eq_failureCount (I : BooleanParityInput.Input) (a : Fin I.variables → Bool) :
    rawViolations (asInstance I) (fun v => valueOf (a v)) = BooleanParityInput.failureCount I a := by
  rw [failureCount_index_sum]
  unfold rawViolations
  apply Finset.sum_congr rfl
  intro r _
  change (if valueOf (a (I.equations.get r).first) +
      valueOf (a (I.equations.get r).second) + valueOf (a (I.equations.get r).third) =
      valueOf (I.equations.get r).rhs then 0 else 1 : Nat) =
    if BooleanParityInput.satisfied (I.equations.get r) a then 0 else 1
  have hp := parity_iff (a (I.equations.get r).first)
    (a (I.equations.get r).second) (a (I.equations.get r).third) (I.equations.get r).rhs
  change BooleanParityInput.satisfied (I.equations.get r) a = true ↔ _ at hp
  cases hs : BooleanParityInput.satisfied (I.equations.get r) a <;> simp_all

/-- Every ZMod2 assignment is covered by the Boolean source quantifier. -/
theorem raw_violations_eq_failureCount_bit (I : BooleanParityInput.Input) (y : Fin I.variables → ZMod 2) :
    rawViolations (asInstance I) y = failureCount I (fun v => bitOf (y v)) := by
  simpa only [valueOf_bitOf] using
    raw_violations_eq_failureCount I (fun v => bitOf (y v))

theorem failureRate_cast (I : BooleanParityInput.Input) (a : Fin I.variables → Bool) :
    (BooleanParityInput.failureRate I a : ℝ) = (BooleanParityInput.failureCount I a : ℝ) / (I.equations.length : ℝ) := by
  simp only [BooleanParityInput.failureRate, Rat.cast_div, Rat.cast_natCast]

theorem raw_no_of_failureRate (I : BooleanParityInput.Input) (rho : ℚ)
    (hno : ∀ a : Fin I.variables → Bool, rho ≤ BooleanParityInput.failureRate I a) :
    RawNoPromise (asInstance I) (rho : ℝ) := by
  intro y
  rw [raw_violations_eq_failureCount_bit]
  have h := (Rat.cast_le (K := ℝ)).mpr (hno (fun v => bitOf (y v)))
  rw [failureRate_cast] at h
  exact (le_div_iff₀ (by exact_mod_cast rows_positive I :
    (0 : ℝ) < (I.equations.length : ℝ))).mp h

theorem raw_yes_of_failureRate (I : BooleanParityInput.Input) (a : Fin I.variables → Bool) (eps : ℚ)
    (hyes : BooleanParityInput.failureRate I a ≤ eps) :
    (rawViolations (asInstance I) (fun v => valueOf (a v)) : ℝ) ≤
      (eps : ℝ) * (I.equations.length : ℝ) := by
  rw [raw_violations_eq_failureCount]
  have h := (Rat.cast_le (K := ℝ)).mpr hyes
  rw [failureRate_cast] at h
  exact (div_le_iff₀ (by exact_mod_cast rows_positive I :
    (0 : ℝ) < (I.equations.length : ℝ))).mp h

/-- Apply the concrete cloud gap transfer with the fixed raw NO constant. -/
theorem actual_no_of_failure_quarter (I : BooleanParityInput.Input)
    (hno : ∀ a : Fin I.variables → Bool, (1 / 4 : ℚ) ≤ BooleanParityInput.failureRate I a) :
    ActualNoPromise (asInstance I) (outputGap (1 / 4)) := by
  apply raw_no_implies_actual_no (asInstance I) (1 / 4) (by norm_num) (rows_positive I)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using raw_no_of_failureRate I (1 / 4) hno

/-- The same generated output admits the exact lifted YES assignment. -/
theorem actual_yes_of_failureRate (I : BooleanParityInput.Input) (a : Fin I.variables → Bool) (eps : ℚ)
    (heps : 0 ≤ eps) (hyes : BooleanParityInput.failureRate I a ≤ eps) :
    ((asInstance I).violations (liftAssignment (asInstance I) (fun v => valueOf (a v))) : ℝ) ≤
      (eps : ℝ) * ((asInstance I).rows.length : ℝ) := by
  exact raw_yes_implies_actual_yes (asInstance I) (fun v => valueOf (a v))
    (eps : ℝ) (by exact_mod_cast heps) (raw_yes_of_failureRate I a eps hyes)

end
end PvNP.RealizableHardness.ActualBooleanOccurrenceSource
