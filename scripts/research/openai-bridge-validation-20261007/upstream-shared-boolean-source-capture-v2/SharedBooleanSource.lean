import OAI.Quantyra.UnclonedBinarySource
import PvNP.RealizableHardness.BooleanParityInput

/-! Exact typed, semantic and serialized-output transport of the captured
uncloned source. This module belongs to the original upstream environment. -/
namespace OAI.UniqueGamesTheorem.Outer.QuantyraSharedBooleanSource

open OAI.UniqueGamesTheorem.Foundations Target Complexity PCP
open OAI.UniqueGamesTheorem.Reduction ActualSource
open PvNP.RealizableHardness
open MachineFiniteAlphabet

set_option autoImplicit false
noncomputable section

def toSharedEquation {Name : Type} (e : CloneGap.Equation Name) :
    BooleanParityInput.Equation Name := ⟨e.first, e.second, e.third, e.rhs⟩

def fromSharedEquation {Name : Type} (e : BooleanParityInput.Equation Name) :
    CloneGap.Equation Name := ⟨e.first, e.second, e.third, e.rhs⟩

theorem equation_from_to {Name : Type} (e : CloneGap.Equation Name) :
    fromSharedEquation (toSharedEquation e) = e := by cases e; rfl

theorem equation_to_from {Name : Type} (e : BooleanParityInput.Equation Name) :
    toSharedEquation (fromSharedEquation e) = e := by cases e; rfl

def toShared (I : SourceEncoding.Input) : BooleanParityInput.Input where
  variables := I.variables
  equations := I.equations.map toSharedEquation
  nonempty := by
    apply List.length_pos_iff.mp
    simpa only [List.length_map] using List.length_pos_iff.mpr I.nonempty

def fromShared (I : BooleanParityInput.Input) : SourceEncoding.Input where
  variables := I.variables
  equations := I.equations.map fromSharedEquation
  nonempty := by
    apply List.length_pos_iff.mp
    simpa only [List.length_map] using List.length_pos_iff.mpr I.nonempty

theorem input_from_to (I : SourceEncoding.Input) : fromShared (toShared I) = I := by
  cases I
  simp [toShared, fromShared, List.map_map, Function.comp_def, equation_from_to]

theorem input_to_from (I : BooleanParityInput.Input) : toShared (fromShared I) = I := by
  cases I
  simp [toShared, fromShared, List.map_map, Function.comp_def, equation_to_from]

theorem satisfied_toShared {Name : Type} (e : CloneGap.Equation Name) (a : Name → Bool) :
    BooleanParityInput.satisfied (toSharedEquation e) a = CloneGap.satisfied e a := rfl

/-- The complete ordered word sequence, including all duplicate entries, is unchanged. -/
theorem inputWords_toShared (I : SourceEncoding.Input) :
    BooleanParityInput.inputWords (toShared I) = SourceEncoding.inputWords I := by
  simp [BooleanParityInput.inputWords, SourceEncoding.inputWords, toShared,
    List.flatMap_map, BooleanParityInput.equationWords, SourceEncoding.equationWords,
    toSharedEquation]

theorem inputWords_fromShared (I : BooleanParityInput.Input) :
    SourceEncoding.inputWords (fromShared I) = BooleanParityInput.inputWords I := by
  simp [BooleanParityInput.inputWords, SourceEncoding.inputWords, fromShared,
    List.flatMap_map, BooleanParityInput.equationWords, SourceEncoding.equationWords,
    fromSharedEquation]

theorem failureCount_toShared (I : SourceEncoding.Input) (a : Fin I.variables → Bool) :
    BooleanParityInput.failureCount (toShared I) a =
      I.equations.countP (fun e => !(CloneGap.satisfied e a)) := by
  simpa only [BooleanParityInput.failureCount, toShared, List.countP_map]

private theorem complement_count {V : Type*} (l : List V) (p : V → Bool) :
    l.countP (fun v => !(p v)) + l.countP p = l.length := by
  induction l with
  | nil => rfl
  | cons v l ih => cases h : p v <;> simp [h] at * <;> omega

theorem failureRate_toShared (I : SourceEncoding.Input) (a : Fin I.variables → Bool) :
    BooleanParityInput.failureRate (toShared I) a = (HastadSource.asSource I).failure a := by
  have hcountNat := complement_count I.equations (fun e => CloneGap.satisfied e a)
  have hcount : (I.equations.countP (fun e => !(CloneGap.satisfied e a)) : ℚ) +
      (I.equations.countP (fun e => CloneGap.satisfied e a) : ℚ) =
      (I.equations.length : ℚ) := by exact_mod_cast hcountNat
  have hlen : (0 : ℚ) < (I.equations.length : ℚ) := by
    exact_mod_cast List.length_pos_iff.mpr I.nonempty
  have hsum : BooleanParityInput.failureRate (toShared I) a + HastadSource.success I a = 1 := by
    unfold BooleanParityInput.failureRate
    rw [failureCount_toShared]
    have hlength : (toShared I).equations.length = I.equations.length := List.length_map
    rw [hlength]
    unfold HastadSource.success
    rw [← add_div, hcount, div_self (ne_of_gt hlen)]
  have horiginal := HastadSource.failure_add_success I a
  linarith

def sharedBits (I : BooleanParityInput.Input) : List Bool :=
  SourceEncoding.inputBits (fromShared I)

theorem sharedBits_toShared (I : SourceEncoding.Input) :
    sharedBits (toShared I) = SourceEncoding.inputBits I := by
  rw [sharedBits, input_from_to]

/-- Same transition machine, alphabets and time polynomial; only output typing changes. -/
def transportComputation {ε : ℚ} (R : QuantyraUnclonedBinarySource.Reduction ε) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) sharedBits
      (fun word => toShared (R.reduce word)) where
  toTM2ComputableAux := R.computation.toTM2ComputableAux
  time := R.computation.time
  outputsFun word := by
    simpa only [sharedBits_toShared] using R.computation.outputsFun word

theorem transportComputation_finite {ε : ℚ} (R : QuantyraUnclonedBinarySource.Reduction ε) :
    FiniteAlphabet (transportComputation R).tm := R.finiteAlphabet

structure Reduction (ε : ℚ) where
  reduce : List Bool → BooleanParityInput.Input
  completeness : ∀ word, BinaryLanguage.language word →
    ∃ a, BooleanParityInput.failureRate (reduce word) a ≤ ε
  soundness : ∀ word, ¬ BinaryLanguage.language word →
    ∀ a, 1 / 4 ≤ BooleanParityInput.failureRate (reduce word) a
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) sharedBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

def transport {ε : ℚ} (R : QuantyraUnclonedBinarySource.Reduction ε) : Reduction ε where
  reduce word := toShared (R.reduce word)
  completeness word yes := by
    obtain ⟨a, ha⟩ := R.completeness word yes
    exact ⟨a, by simpa only [failureRate_toShared] using ha⟩
  soundness word no a := by
    simpa only [failureRate_toShared] using R.soundness word no a
  computation := transportComputation R
  finiteAlphabet := transportComputation_finite R

theorem exists_reduction (ε : ℚ) (positive : 0 < ε) : Nonempty (Reduction ε) := by
  obtain ⟨R⟩ := QuantyraUnclonedBinarySource.exists_reduction ε positive
  exact ⟨transport R⟩

end
end OAI.UniqueGamesTheorem.Outer.QuantyraSharedBooleanSource
