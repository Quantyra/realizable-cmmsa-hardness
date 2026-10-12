import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Complexitylib.Classes.P.Cobham.Vec
import TM2CobhamConfigurationCode

/-!
# Fixed-capacity stack fields for the TM2 Cobham iterator

Each genuine symbol is a one-hot block with a leading true bit; the blank
sentinel is the all-zero block of the same positive width. A stack field has a fixed number of cells. Its
single-cell push and pop operations are Cobham functions and preserve the field
width. Push truncates at the fixed capacity; the actual-run invariant must prove
that this truncation never occurs before the external clock horizon.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

open Complexity.Cobham

/-- The sentinel-extended cell type is nonempty, even when every physical
stack alphabet is empty. -/
abbrev StackCell (tm : Turing.FinTM2) := Option (TaggedStackSymbol tm)

noncomputable def stackCellWidth (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Nat := taggedAlphabetWidth tm finiteAlphabets + 1

noncomputable def stackCellCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cell : StackCell tm) : List Bool := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  cases cell with
  | none => exact false :: List.replicate (taggedAlphabetWidth tm finiteAlphabets) false
  | some symbol => exact true :: oneHotCode symbol

@[simp] theorem stackCellCode_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cell : StackCell tm) :
    (stackCellCode tm finiteAlphabets cell).length = stackCellWidth tm finiteAlphabets := by
  cases cell with
  | none => simp [stackCellCode, stackCellWidth]
  | some symbol =>
      letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
      simp [stackCellCode, stackCellWidth, oneHotCode]

theorem stackCellCode_injective (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Function.Injective (stackCellCode tm finiteAlphabets) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some symbol =>
          have hfalse : (false : Bool) = true := by
            have hhead := congrArg List.head? h
            simp [stackCellCode, stackCellWidth] at hhead
          cases hfalse
  | some symbolA =>
      cases b with
      | none =>
          have hfalse : true = (false : Bool) := by
            have hhead := congrArg List.head? h
            simp [stackCellCode, stackCellWidth] at hhead
          cases hfalse
      | some symbolB =>
          have htail : oneHotCode symbolA = oneHotCode symbolB := by
            injection h with htail
            exact htail
          exact congrArg some (oneHotCode_injective htail)

theorem stackCellWidth_pos (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    0 < stackCellWidth tm finiteAlphabets := by
  simp [stackCellWidth]

/-- A stack is truncated to its capacity and padded with the distinct
`none` sentinel cell. -/
def boundedStackCells (tm : Turing.FinTM2) (capacity : Nat)
    (stack : List (TaggedStackSymbol tm)) : List (StackCell tm) :=
  match capacity, stack with
  | 0, _ => []
  | n + 1, [] => none :: boundedStackCells tm n []
  | n + 1, symbol :: rest => some symbol :: boundedStackCells tm n rest

theorem boundedStackCells_length (tm : Turing.FinTM2) (capacity : Nat)
    (stack : List (TaggedStackSymbol tm)) :
    (boundedStackCells tm capacity stack).length = capacity := by
  induction capacity generalizing stack with
  | zero => simp [boundedStackCells]
  | succ capacity ih => cases stack <;> simp [boundedStackCells, ih]

/-- Encode all fixed-capacity cells, including the all-zero sentinels. -/
noncomputable def boundedStackCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm)) : List Bool :=
  ((boundedStackCells tm capacity stack).map (stackCellCode tm finiteAlphabets)).flatten

@[simp] theorem boundedStackCode_succ_cons (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (symbol : TaggedStackSymbol tm) (stack : List (TaggedStackSymbol tm)) :
    boundedStackCode tm finiteAlphabets (capacity + 1) (symbol :: stack) =
      stackCellCode tm finiteAlphabets (some symbol) ++
        boundedStackCode tm finiteAlphabets capacity stack := by
  simp [boundedStackCode, boundedStackCells]

@[simp] theorem boundedStackCode_succ_nil (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) :
    boundedStackCode tm finiteAlphabets (capacity + 1) [] =
      stackCellCode tm finiteAlphabets none ++ boundedStackCode tm finiteAlphabets capacity [] := by
  simp [boundedStackCode, boundedStackCells]

/-- The physical-stack payload as tagged cells from the common finite alphabet. -/
def taggedStack (tm : Turing.FinTM2) (k : tm.K) (stack : List (tm.Γ k)) :
    List (TaggedStackSymbol tm) :=
  stack.map fun symbol => ⟨k, symbol⟩

/-- The actual upstream `.push` constructor updates the selected stack before
continuing into its nested statement. -/
theorem stepAux_push_eq (tm : Turing.FinTM2) (k : tm.K)
    (f : tm.σ → tm.Γ k) (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux (Turing.TM2.Stmt.push k f next) state stacks =
      Turing.TM2.stepAux next state (Function.update stacks k (f state :: stacks k)) := by
  rfl

theorem encoded_push_continuation_stack_field (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (k : tm.K) (f : tm.σ → tm.Γ k)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (state : tm.σ)
    (stacks : ∀ j, List (tm.Γ j)) :
    boundedStackCode tm finiteAlphabets (capacity + 1)
      (taggedStack tm k ((Function.update stacks k (f state :: stacks k)) k)) =
      stackCellCode tm finiteAlphabets (some ⟨k, f state⟩) ++
        boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (stacks k)) := by
  simp [taggedStack, boundedStackCode_succ_cons]

/-- The actual upstream `.pop` constructor updates the selected stack to its
tail and passes the popped head to the continuation state function. -/
theorem stepAux_pop_eq (tm : Turing.FinTM2) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux (Turing.TM2.Stmt.pop k f next) state stacks =
      Turing.TM2.stepAux next (f state (stacks k).head?)
        (Function.update stacks k (stacks k).tail) := by
  rfl

theorem stepAux_peek_eq (tm : Turing.FinTM2) (k : tm.K)
    (f : tm.σ → Option (tm.Γ k) → tm.σ) (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux (Turing.TM2.Stmt.peek k f next) state stacks =
      Turing.TM2.stepAux next (f state (stacks k).head?) stacks := by
  rfl

theorem stepAux_load_eq (tm : Turing.FinTM2)
    (f : tm.σ → tm.σ) (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux (Turing.TM2.Stmt.load f next) state stacks =
      Turing.TM2.stepAux next (f state) stacks := by
  rfl

theorem stepAux_branch_eq (tm : Turing.FinTM2)
    (condition : tm.σ → Bool) (yes no : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux (Turing.TM2.Stmt.branch condition yes no) state stacks =
      if condition state then Turing.TM2.stepAux yes state stacks
      else Turing.TM2.stepAux no state stacks := by
  rfl

theorem stepAux_goto_eq (tm : Turing.FinTM2) (f : tm.σ → tm.Λ)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux (Turing.TM2.Stmt.goto f) state stacks =
      ⟨some (f state), state, stacks⟩ := by
  rfl

theorem stepAux_halt_eq (tm : Turing.FinTM2)
    (state : tm.σ) (stacks : ∀ j, List (tm.Γ j)) :
    Turing.TM2.stepAux Turing.TM2.Stmt.halt state stacks =
      ⟨none, state, stacks⟩ := by
  rfl

theorem encoded_pop_continuation_stack_field (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (state : tm.σ)
    (stacks : ∀ j, List (tm.Γ j)) :
    boundedStackCode tm finiteAlphabets capacity
      (taggedStack tm k ((Function.update stacks k (stacks k).tail) k)) =
      boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (stacks k).tail) := by
  simp

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
  cell ++ field.take (field.length - cell.length)

theorem pushCellField_length (cell field : List Bool) (h : cell.length ≤ field.length) :
    (pushCellField cell field).length = field.length := by
  simp [pushCellField]
  omega

theorem pushCellField_mem (cell : List Bool) :
    Cobham fun v : Fin 1 → List Bool => pushCellField cell (v 0) := by
  have hdrop : Cobham fun v : Fin 1 → List Bool => (v 0).drop cell.length :=
    dropCell_mem cell.length
  have htake : Cobham fun v : Fin 1 → List Bool =>
      (v 0).take ((v 0).drop cell.length).length :=
    Cobham.takeFn hdrop (Cobham.proj 0)
  exact (Cobham.appendFn (Cobham.const cell) htake).of_eq fun _ => by
    simp [pushCellField, List.length_drop]

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
    clockLength * (∑ _k : tm.K, Runtime.programPushBound tm) +
    Fintype.card (Option tm.Λ × tm.σ) + 1

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
