import Complexitylib.Classes.P.Cobham.Algebra
import Complexitylib.Classes.P.Cobham.Vec
import TM2CobhamConfigurationCode

/-!
# Fixed-capacity stack fields for the TM2 Cobham iterator

Each symbol, including the blank sentinel, is a one-hot block from one finite
option-tagged alphabet. A stack field has a fixed number of cells. Its
single-cell push and pop operations are Cobham functions and preserve the field
width. The caller chooses capacity from the input and the external clock word;
the full machine transition must send any attempted overflow to an absorbing
overflow code.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

open Complexity.Cobham

/-- The sentinel-extended alphabet has at least one element, even when every
physical stack alphabet is empty. -/
abbrev StackCell (tm : Turing.FinTM2) := Option (TaggedStackSymbol tm)

noncomputable def stackCellFintype (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Fintype (StackCell tm) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  exact inferInstance

noncomputable def stackCellWidth (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Nat := by
  letI : Fintype (StackCell tm) := stackCellFintype tm finiteAlphabets
  exact Fintype.card (StackCell tm)

noncomputable def stackCellCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cell : StackCell tm) : List Bool := by
  letI : Fintype (StackCell tm) := stackCellFintype tm finiteAlphabets
  exact oneHotCode cell

@[simp] theorem stackCellCode_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cell : StackCell tm) :
    (stackCellCode tm finiteAlphabets cell).length = stackCellWidth tm finiteAlphabets := by
  simp [stackCellCode, stackCellWidth, stackCellFintype]

theorem stackCellWidth_pos (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    0 < stackCellWidth tm finiteAlphabets := by
  letI : Fintype (StackCell tm) := stackCellFintype tm finiteAlphabets
  exact Fintype.card_pos_iff.mpr ⟨none⟩

/-- A stack is truncated to its capacity and padded with the distinct
`none` sentinel cell. -/
def boundedStackCells (tm : Turing.FinTM2) (capacity : Nat)
    (stack : List (TaggedStackSymbol tm)) :
    List (StackCell tm) :=
  (stack.take capacity).map some ++
    List.replicate (capacity - (stack.take capacity).length) none

theorem boundedStackCells_length (tm : Turing.FinTM2) (capacity : Nat)
    (stack : List (TaggedStackSymbol tm)) :
    (boundedStackCells tm capacity stack).length = capacity := by
  simp [boundedStackCells]
  omega

/-- Encode all fixed-capacity cells, including the sentinel, in the finite
option-tagged one-hot alphabet. -/
noncomputable def boundedStackCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm)) : List Bool :=
  ((boundedStackCells tm capacity stack).map (stackCellCode tm finiteAlphabets)).flatten

theorem boundedStackCode_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm)) :
    (boundedStackCode tm finiteAlphabets capacity stack).length =
      capacity * stackCellWidth tm finiteAlphabets := by
  simp [boundedStackCode, boundedStackCells_length, stackCellCode_length]

/-- Drop one fixed-width cell. This total operation is in Cobham's class by
`dropFn` with a constant ruler. -/
theorem dropCell_mem (width : Nat) :
    Cobham fun v : Fin 1 → List Bool => (v 0).drop width := by
  have hr : Cobham (fun _ : Fin 1 → List Bool => List.replicate width false) := Cobham.const _
  exact Cobham.dropFn hr (Cobham.proj 0)

/-- Prepend a fixed symbol cell and discard the last cell, preserving the
length of every well-formed nonempty fixed-width stack field. -/
def pushCellField (cell field : List Bool) : List Bool :=
  cell ++ field.drop cell.length

theorem pushCellField_length (cell field : List Bool) (h : cell.length ≤ field.length) :
    (pushCellField cell field).length = field.length := by
  simp [pushCellField]
  omega

theorem pushCellField_mem (cell : List Bool) :
    Cobham fun v : Fin 1 → List Bool => pushCellField cell (v 0) := by
  exact (Cobham.appendFn (Cobham.const cell) (dropCell_mem cell.length)).of_eq fun _ => rfl

/-- Remove the first cell and append a fixed sentinel cell. -/
def popCellField (width : Nat) (sentinel field : List Bool) : List Bool :=
  field.drop width ++ sentinel

theorem popCellField_length (width : Nat) (sentinel field : List Bool)
    (hwidth : width ≤ field.length) (hsentinel : sentinel.length = width) :
    (popCellField width sentinel field).length = field.length := by
  simp [popCellField]
  omega

theorem popCellField_mem (width : Nat) (sentinel : List Bool) :
    Cobham fun v : Fin 1 → List Bool => popCellField width sentinel (v 0) := by
  exact (Cobham.appendFn (dropCell_mem width) (Cobham.const sentinel)).of_eq fun _ => rfl

/-- A fixed stack-field capacity large enough for every stack through the
external clock horizon. The extra cell separates the maximum reachable size
from the overflow boundary. -/
def fixedStackCapacity (tm : Turing.FinTM2) (inputLength clockLength : Nat) : Nat :=
  Fintype.card tm.K * inputLength +
    clockLength * (∑ _k : tm.K, Runtime.programPushBound tm) + 1

theorem initial_totalStackLength_le (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) :
    totalStackLength tm (Turing.initList tm input) ≤
      Fintype.card tm.K * input.length := by
  unfold totalStackLength
  calc
    (∑ k : tm.K, ((Turing.initList tm input).stk k).length) ≤
        ∑ _k : tm.K, input.length := by
      apply Finset.sum_le_sum
      intro k hk
      exact Runtime.initialStackLength tm input k
    _ = Fintype.card tm.K * input.length := by simp

theorem stackLength_le_totalStackLength (tm : Turing.FinTM2) (cfg : tm.Cfg)
    (k : tm.K) :
    (cfg.stk k).length ≤ totalStackLength tm cfg := by
  unfold totalStackLength
  exact Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_univ k)

/-- Every actual iterated configuration through the chosen external clock fits
inside every fixed-capacity stack field. The bounded transition's overflow arm
is therefore unreachable over this horizon. -/
theorem iterate_absorbingStep_stackLength_lt_capacity (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (clockLength : Nat) (k : tm.K)
    (clock : Nat) (hclock : clock ≤ clockLength) :
    (((absorbingStep tm)^[clock] (Turing.initList tm input)).stk k).length <
      fixedStackCapacity tm input.length clockLength := by
  have htotal := iterate_absorbingStep_stackLength_le tm clock (Turing.initList tm input)
  have hstack := stackLength_le_totalStackLength tm
    ((absorbingStep tm)^[clock] (Turing.initList tm input)) k
  have hinitial := initial_totalStackLength_le tm input
  have hbudget : clock * (∑ _k : tm.K, Runtime.programPushBound tm) ≤
      clockLength * (∑ _k : tm.K, Runtime.programPushBound tm) :=
    Nat.mul_le_mul_right _ hclock
  unfold fixedStackCapacity
  omega

/-- The bounded-cell encoding has fixed serialized width, suitable for
`blockFn`-addressed fields in a configuration code. -/
theorem boundedStackCode_fixed_width (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm)) :
    (boundedStackCode tm finiteAlphabets capacity stack).length =
      capacity * stackCellWidth tm finiteAlphabets :=
  boundedStackCode_length tm finiteAlphabets capacity stack

end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer
