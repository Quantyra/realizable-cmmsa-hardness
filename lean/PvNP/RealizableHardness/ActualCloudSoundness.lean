import PvNP.RealizableHardness.ActualEqualityCloud

/-! Uncompiled source draft: all-port majority and actual-cloud soundness.
No source hardness, encoded FP, occurrence charging or final gap is assumed. -/
namespace PvNP.RealizableHardness.ActualCloudSoundness
open ActualGraphEdges ActualEqualityCloud
open scoped BigOperators
set_option autoImplicit false
noncomputable section

def toBool (z : ZMod 2) : Bool := decide (z = 1)
def fromBool (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toBool_fromBool : ∀ b : Bool, toBool (fromBool b) = b := by decide
theorem fromBool_toBool : ∀ z : ZMod 2, fromBool (toBool z) = z := by decide

theorem toBool_injective : Function.Injective toBool := by
  intro a b h
  have he := congrArg fromBool h
  simpa only [fromBool_toBool] using he

@[simp] theorem toBool_eq_iff (a b : ZMod 2) : toBool a = toBool b ↔ a = b :=
  toBool_injective.eq_iff

section FiniteMajority
variable {X : Type*} [Fintype X]

def trueCount (S : X → Bool) : Nat := (Finset.univ.filter (fun p => S p = true)).card
def falseCount (S : X → Bool) : Nat := (Finset.univ.filter (fun p => S p = false)).card

/-- False (hence field zero) wins ties, including an empty domain. -/
def majorityBool (S : X → Bool) : Bool := if trueCount S ≤ falseCount S then false else true

def minorityBool (S : X → Bool) : Nat :=
  (Finset.univ.filter (fun p => S p ≠ majorityBool S)).card

theorem minorityBool_eq_min (S : X → Bool) :
    minorityBool S = min (trueCount S) (falseCount S) := by
  classical
  have hf : (Finset.univ.filter (fun p => S p ≠ false)) =
      (Finset.univ.filter (fun p => S p = true)) := by
    ext p
    cases S p <;> simp
  have ht : (Finset.univ.filter (fun p => S p ≠ true)) =
      (Finset.univ.filter (fun p => S p = false)) := by
    ext p
    cases S p <;> simp
  by_cases h : trueCount S ≤ falseCount S
  · unfold minorityBool majorityBool
    rw [if_pos h, hf, min_eq_left h]
    rfl
  · unfold minorityBool majorityBool
    rw [if_neg h, ht, min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    rfl

theorem trueCount_real (S : X → Bool) :
    (trueCount S : Real) = PortCycleReplacement.count S := by
  classical
  unfold trueCount PortCycleReplacement.count
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  cases S p <;> norm_num [PortCycleReplacement.bit]

theorem falseCount_real (S : X → Bool) :
    (falseCount S : Real) = PortCycleReplacement.count (fun p => !(S p)) := by
  have h : falseCount S = trueCount (fun p => !(S p)) := by
    unfold falseCount trueCount
    congr 1
    ext p
    cases S p <;> simp
  rw [h, trueCount_real]

theorem minorityBool_eq_smallSide (S : X → Bool) :
    (minorityBool S : Real) = PortCycleReplacement.smallSide S := by
  rw [minorityBool_eq_min, Nat.cast_min, trueCount_real, falseCount_real]
  rfl

theorem majorityBool_tie (S : X → Bool) (h : trueCount S = falseCount S) :
    majorityBool S = false := by simp [majorityBool, h]

theorem majorityBool_empty [IsEmpty X] (S : X → Bool) : majorityBool S = false := by
  simp [majorityBool, trueCount, falseCount]

end FiniteMajority

def portBits {n : Nat} (x : GlobalVar n → ZMod 2) : Vertex n → Bool :=
  fun p => toBool (x (Sum.inl p))

def majority {n : Nat} (x : GlobalVar n → ZMod 2) : ZMod 2 :=
  fromBool (majorityBool (portBits x))

/-- Every actual graph port is counted, including unanchored dummy ports. -/
def minority {n : Nat} (x : GlobalVar n → ZMod 2) : Nat :=
  (Finset.univ.filter (fun p : Vertex n => x (Sum.inl p) ≠ majority x)).card

theorem minority_eq_bool {n : Nat} (x : GlobalVar n → ZMod 2) :
    minority x = minorityBool (portBits x) := by
  classical
  unfold minority minorityBool
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := toBool_eq_iff (x (Sum.inl p)) (majority x)
  simpa only [majority, toBool_fromBool, portBits] using not_congr h.symm

theorem minority_eq_smallSide {n : Nat} (x : GlobalVar n → ZMod 2) :
    (minority x : Real) = PortCycleReplacement.smallSide (portBits x) := by
  rw [minority_eq_bool, minorityBool_eq_smallSide]

theorem majority_zero (x : GlobalVar 0 → ZMod 2) : majority x = 0 := by
  have h : majorityBool (portBits x) = false := majorityBool_empty _
  rw [majority, h]
  rfl

def disagreeEdges {n : Nat} (x : GlobalVar n → ZMod 2) : Finset (Edge n) :=
  Finset.univ.filter (fun e => x (Sum.inl e.val.1) ≠ x (Sum.inl (reverse e.val).1))

/-- Equality of the actual retained-orbit count, not an endpoint-pair quotient. -/
theorem disagreeEdges_card {n : Nat} (x : GlobalVar n → ZMod 2) :
    (disagreeEdges x).card = (crossing n (portBits x)).card := by
  classical
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    apply Finset.mem_filter.mpr
    refine ⟨mem_representatives.mpr e.property, ?_⟩
    have hn := (Finset.mem_filter.mp he).2
    simpa only [portBits, ne_eq, toBool_eq_iff] using hn
  · intro e _ f _ h
    exact Subtype.ext h
  · intro d hd
    have hr := mem_representatives.mp (Finset.mem_filter.mp hd).1
    refine ⟨⟨d,hr⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [portBits, ne_eq, toBool_eq_iff] using (Finset.mem_filter.mp hd).2

theorem mismatch_sum_eq_crossing {n : Nat} (x : GlobalVar n → ZMod 2) :
    (∑ e : Edge n, EqualityGadget.mismatch
      (x (Sum.inl e.val.1)) (x (Sum.inl (reverse e.val).1))) =
        (crossing n (portBits x)).card := by
  rw [← disagreeEdges_card x]
  unfold disagreeEdges
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : x (Sum.inl e.val.1) = x (Sum.inl (reverse e.val).1) <;>
    simp [EqualityGadget.mismatch, h]

/-- Actual generated row violations dominate the fixed expansion coefficient
multiplied by the actual all-port minority count, for every assignment. -/
theorem rowsViolations_lower {n : Nat} (x : GlobalVar n → ZMod 2) :
    FixedPortCycleFamily.kappa * (minority x : Real) ≤ (rowsViolations x : Real) := by
  have hl := ActualEqualityCloud.rows_lower x
  rw [mismatch_sum_eq_crossing, ← List.countP_eq_length_filter] at hl
  have hlr : ((crossing n (portBits x)).card : Real) ≤ (rowsViolations x : Real) := by
    exact_mod_cast hl
  rw [minority_eq_smallSide]
  exact (crossing_expansion n (portBits x)).trans hlr

end
end PvNP.RealizableHardness.ActualCloudSoundness
