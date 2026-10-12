import TM2CobhamFixedFields

/-!
# Constructor-level fixed stack-field transition equations

These lemmas connect actual upstream `TM2.stepAux` constructors to the
same-capacity bounded fields. Push and pop are the nontrivial stack changes;
all other constructors preserve these fields. The separate state/control
compiler remains an explicit endpoint obligation.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

open Complexity.Cobham

/-- Truncating one extra-capacity encoding back to the current capacity
recovers the current bounded stack encoding. -/
theorem boundedStackCode_succ_take (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm)) :
    (boundedStackCode tm finiteAlphabets (capacity + 1) stack).take
      (capacity * stackCellWidth tm finiteAlphabets) =
        boundedStackCode tm finiteAlphabets capacity stack := by
  induction capacity generalizing stack with
  | zero => simp [boundedStackCode, boundedStackCells]
  | succ capacity ih =>
      cases stack with
      | nil =>
          simp [boundedStackCode, boundedStackCells, stackCellCode_length,
            stackCellWidth]
      | cons symbol rest =>
          rw [boundedStackCode_succ_cons, List.take_append]
          have hcell : (stackCellCode tm finiteAlphabets (some symbol)).length =
              stackCellWidth tm finiteAlphabets := by
            simp
          have htake : (stackCellCode tm finiteAlphabets (some symbol)).length <=
              (capacity + 1) * stackCellWidth tm finiteAlphabets := by
            rw [hcell]
            omega
          simp only [List.take_of_length_le htake]
          have hrest : (capacity + 1) * stackCellWidth tm finiteAlphabets -
                stackCellWidth tm finiteAlphabets =
              capacity * stackCellWidth tm finiteAlphabets := by omega
          rw [hrest, ih]

/-- The actual upstream push update is implemented by the fixed-width Cobham
field operation: prepend the pushed symbol cell and discard the last cell. -/
theorem encoded_stepAux_push_same_capacity (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (k : tm.K) (f : tm.σ -> tm.Γ k)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : forall j, List (tm.Γ j)) :
    boundedStackCode tm finiteAlphabets (capacity + 1)
      (taggedStack tm k ((Function.update stacks k (f state :: stacks k)) k)) =
    pushCellField (stackCellCode tm finiteAlphabets (some (⟨k, f state⟩)))
      (boundedStackCode tm finiteAlphabets (capacity + 1)
        (taggedStack tm k (stacks k))) := by
  rw [encoded_push_continuation_stack_field, pushCellField]
  apply congrArg (List.append (stackCellCode tm finiteAlphabets (some (⟨k, f state⟩))))
  rw [show (boundedStackCode tm finiteAlphabets (capacity + 1)
      (taggedStack tm k (stacks k))).length -
        (stackCellCode tm finiteAlphabets (some (⟨k, f state⟩))).length =
      capacity * stackCellWidth tm finiteAlphabets by
    rw [boundedStackCode_length, stackCellCode_length]
    omega]
  exact (boundedStackCode_succ_take tm finiteAlphabets capacity
    (taggedStack tm k (stacks k))).symm

/-- A padded bounded field gains one all-zero cell when its capacity grows,
provided the represented stack fits in the smaller capacity. -/
theorem boundedStackCode_succ_pad (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm))
    (hfit : stack.length <= capacity) :
    boundedStackCode tm finiteAlphabets (capacity + 1) stack =
      boundedStackCode tm finiteAlphabets capacity stack ++
        stackCellCode tm finiteAlphabets none := by
  induction capacity generalizing stack with
  | zero =>
      have hnil : stack = [] := by simpa using hfit
      subst stack
      simp [boundedStackCode, boundedStackCells]
  | succ capacity ih =>
      cases stack with
      | nil =>
          simp [boundedStackCode, boundedStackCells, stackCellCode_length]
      | cons symbol rest =>
          have hrest : rest.length <= capacity := by simpa using hfit
          rw [boundedStackCode_succ_cons, boundedStackCode_succ_cons]
          rw [ih rest hrest]

/-- With the reachable-capacity invariant, the actual upstream pop update is
implemented by dropping the top cell and restoring an all-zero sentinel. -/
theorem encoded_stepAux_pop_same_capacity (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (k : tm.K)
    (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : forall j, List (tm.Γ j))
    (hfit : (stacks k).length <= capacity + 1) :
    boundedStackCode tm finiteAlphabets (capacity + 1)
      (taggedStack tm k ((Function.update stacks k (stacks k).tail) k)) =
    popCellField (stackCellWidth tm finiteAlphabets)
      (stackCellCode tm finiteAlphabets none)
      (boundedStackCode tm finiteAlphabets (capacity + 1)
        (taggedStack tm k (stacks k))) := by
  cases hstack : stacks k with
  | nil =>
      simp [taggedStack, hstack, boundedStackCode_succ_pad,
        popCellField, stackCellCode_length]
  | cons head tail =>
      have htail : tail.length <= capacity := by
        have := hfit
        simp [hstack] at this
        omega
      rw [show (Function.update stacks k (stacks k).tail) k = tail by simp [hstack]]
      rw [boundedStackCode_succ_pad tm finiteAlphabets capacity
        (taggedStack tm k tail) (by simpa [taggedStack] using htail)]
      rw [boundedStackCode_succ_cons]
      simp [taggedStack, hstack, popCellField, stackCellCode_length]
end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer
