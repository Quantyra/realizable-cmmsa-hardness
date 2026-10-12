import TM2CobhamConstructors

/-!
# Finite code dispatch for TM2 register/control transformations

The finite `sigma` and label carriers support actual finite table functions.
All matching prefix branches agree by fixed-width injectivity; malformed
control codes use a total default branch.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

open Complexity.Cobham

noncomputable def finiteCodeTable {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) :
    List (Prod (List Bool) ((Fin 1 -> List Bool) -> List Bool)) :=
  by
    classical
    exact Finset.univ.toList.map (fun a =>
      (oneHotCode a, fun v => f a ++ (v 0).drop (Fintype.card alpha)))

def finiteCodeFn {alpha : Type} [Fintype alpha] (f : alpha -> List Bool)
    (v : Fin 1 -> List Bool) : List Bool :=
  (finiteCodeTable f).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finiteCodeBranch_mem {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) (a : alpha) :
    Complexity.Cobham (fun v : Fin 1 -> List Bool =>
      f a ++ (v 0).drop (Fintype.card alpha)) := by
  have hdrop : Complexity.Cobham (fun v : Fin 1 -> List Bool =>
      (v 0).drop (Fintype.card alpha)) :=
    Complexity.Cobham.dropFn
      (Complexity.Cobham.const (List.replicate (Fintype.card alpha) false))
      (Complexity.Cobham.proj 0)
  exact (Complexity.Cobham.appendFn (Complexity.Cobham.const (f a)) hdrop).of_eq
    (fun _ => rfl)

theorem finiteCodeFn_mem {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) : Complexity.Cobham (finiteCodeFn f) := by
  unfold finiteCodeFn finiteCodeTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 1))
    (Complexity.Cobham.const [])
  intro p hp
  rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩
  exact finiteCodeBranch_mem f a

theorem finiteCodeFn_correct {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) (a : alpha) (payload : List Bool) :
    finiteCodeFn f (fun _ => oneHotCode a ++ payload) = f a ++ payload := by
  let input := oneHotCode a ++ payload
  let vals := (finiteCodeTable f).map (fun p => (p.1, p.2 (fun _ => input)))
  have hexists : Exists (fun p : Prod (List Bool) (List Bool) => List.Mem p vals ∧ p.1 <+: input) := by
    refine ⟨(oneHotCode a, f a ++ payload), ?_, ?_⟩
    · simp [vals, finiteCodeTable, Finset.mem_toList]
    · exact ⟨payload, rfl⟩
  have hall : forall q, List.Mem q vals -> q.1 <+: input -> q.2 = f a ++ payload := by
    intro q hq hprefix
    rcases List.mem_map.mp hq with ⟨p, hp, hqeq⟩
    subst q
    rcases List.mem_map.mp hp with ⟨b, hb, hpeq⟩
    subst p
    rcases hprefix with ⟨suffix, hcat⟩
    have hcode : oneHotCode b = oneHotCode a := by
      have htaken := congrArg (List.take (Fintype.card alpha)) hcat
      simpa [input, oneHotCode_length] using htaken
    have hba : b = a := oneHotCode_injective hcode
    subst b
    simp [input, List.drop_append, oneHotCode_length]
  have hfold := Complexity.Cobham.foldr_table_eq input [] (f a ++ payload)
    vals hexists hall
  unfold finiteCodeFn
  simpa [vals, finiteCodeTable, input, List.foldr_map] using hfold

/-- The actual `load` constructor updates the register while retaining the
finite control label; the field code is implemented by finite table dispatch. -/
theorem encoded_load_control_field (tm : Turing.FinTM2)
    (f : tm.σ -> tm.σ) (label : Option tm.Λ) (state : tm.σ)
    (payload : List Bool) :
    finiteCodeFn (fun pair : Prod (Option tm.Λ) tm.σ =>
      oneHotCode (pair.1, f pair.2))
      (fun _ => oneHotCode (label, state) ++ payload) =
      oneHotCode (label, f state) ++ payload := by
  exact finiteCodeFn_correct
    (fun pair : Prod (Option tm.Λ) tm.σ => oneHotCode (pair.1, f pair.2))
    (label, state) payload

/-- The actual `goto` constructor installs the selected label and keeps the
register value in the encoded control field. -/
theorem encoded_goto_control_field (tm : Turing.FinTM2)
    (f : tm.σ -> tm.Λ) (oldLabel : Option tm.Λ) (state : tm.σ)
    (payload : List Bool) :
    finiteCodeFn (fun pair : Prod (Option tm.Λ) tm.σ =>
      oneHotCode (some (f pair.2), pair.2))
      (fun _ => oneHotCode (oldLabel, state) ++ payload) =
      oneHotCode (some (f state), state) ++ payload := by
  exact finiteCodeFn_correct
    (fun pair : Prod (Option tm.Λ) tm.σ =>
      oneHotCode (some (f pair.2), pair.2))
    (oldLabel, state) payload

/-- The actual `halt` constructor installs the absorbing no-label control
value and preserves the register. -/
theorem encoded_halt_control_field (tm : Turing.FinTM2)
    (oldLabel : Option tm.Λ) (state : tm.σ) (payload : List Bool) :
    finiteCodeFn (fun pair : Prod (Option tm.Λ) tm.σ =>
      oneHotCode (none, pair.2))
      (fun _ => oneHotCode (oldLabel, state) ++ payload) =
      oneHotCode (none, state) ++ payload := by
  exact finiteCodeFn_correct
    (fun pair : Prod (Option tm.Λ) tm.σ => oneHotCode (none, pair.2))
    (oldLabel, state) payload

/-- The actual `branch` condition is obtained by finite dispatch from the
encoded label/register pair. -/
theorem encoded_branch_condition_field (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool) (label : Option tm.Λ)
    (state : tm.σ) (payload : List Bool) :
    finiteCodeFn (fun pair : Prod (Option tm.Λ) tm.σ => [condition pair.2])
      (fun _ => oneHotCode (label, state) ++ payload) =
      [condition state] ++ payload := by
  exact finiteCodeFn_correct
    (fun pair : Prod (Option tm.Λ) tm.σ => [condition pair.2])
    (label, state) payload

/-- Apply a finite control-state map to field zero of a serialized
configuration, retaining every stack field. -/
def controlFieldMap (tm : Turing.FinTM2) (ruler state : List Bool)
    (f : Prod (Option tm.Λ) tm.σ -> Prod (Option tm.Λ) tm.σ) : List Bool :=
  replaceFixedField ruler state
    (finiteCodeFn (fun pair => oneHotCode (f pair))
      (fun _ => fixedFieldAt ruler state 0)) 0

theorem controlFieldMap_mem (tm : Turing.FinTM2)
    (f : Prod (Option tm.Λ) tm.σ -> Prod (Option tm.Λ) tm.σ) :
    Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      controlFieldMap tm (v 0) (v 1) f) := by
  have hread : Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      fixedFieldAt (v 0) (v 1) 0) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem 0)
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have hlookup : Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      finiteCodeFn (fun pair => oneHotCode (f pair))
        (fun _ => fixedFieldAt (v 0) (v 1) 0)) :=
    (Complexity.Cobham.comp (finiteCodeFn_mem (fun pair => oneHotCode (f pair)))
      (gs := ![hread])).of_eq (fun _ => rfl)
  exact (Complexity.Cobham.comp (replaceFixedField_mem 0)
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1, hlookup])).of_eq
      (fun _ => rfl)

theorem controlFieldMap_correct (tm : Turing.FinTM2)
    (ruler state : List Bool)
    (f : Prod (Option tm.Λ) tm.σ -> Prod (Option tm.Λ) tm.σ)
    (control : Prod (Option tm.Λ) tm.σ) (payload : List Bool)
    (hread : fixedFieldAt ruler state 0 = oneHotCode control ++ payload) :
    controlFieldMap tm ruler state f =
      replaceFixedField ruler state (oneHotCode (f control) ++ payload) 0 := by
  unfold controlFieldMap
  rw [hread, finiteCodeFn_correct]
/-- A finite table lookup which discards the encoded key and padding. -/
noncomputable def finiteValueTable {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) :
    List (Prod (List Bool) ((Fin 1 -> List Bool) -> List Bool)) := by
  classical
  exact Finset.univ.toList.map (fun a => (oneHotCode a, fun _ => f a))

def finiteValueFn {alpha : Type} [Fintype alpha] (f : alpha -> List Bool)
    (v : Fin 1 -> List Bool) : List Bool :=
  (finiteValueTable f).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finiteValueFn_mem {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) : Complexity.Cobham (finiteValueFn f) := by
  unfold finiteValueFn finiteValueTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 1))
    (Complexity.Cobham.const [])
  intro p hp
  rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩
  exact Complexity.Cobham.const (f a)

theorem finiteValueFn_correct {alpha : Type} [Fintype alpha]
    (f : alpha -> List Bool) (a : alpha) (payload : List Bool) :
    finiteValueFn f (fun _ => oneHotCode a ++ payload) = f a := by
  let input := oneHotCode a ++ payload
  let vals := (finiteValueTable f).map (fun p => (p.1, p.2 (fun _ => input)))
  have hexists : Exists (fun p : Prod (List Bool) (List Bool) =>
      List.Mem p vals ∧ p.1 <+: input) := by
    refine ⟨(oneHotCode a, f a), ?_, ?_⟩
    · simp [vals, finiteValueTable, Finset.mem_toList]
    · exact ⟨payload, rfl⟩
  have hall : forall q, List.Mem q vals -> q.1 <+: input -> q.2 = f a := by
    intro q hq hprefix
    rcases List.mem_map.mp hq with ⟨p, hp, hqeq⟩
    subst q
    rcases List.mem_map.mp hp with ⟨b, hb, hpeq⟩
    subst p
    rcases hprefix with ⟨suffix, hcat⟩
    have hcode : oneHotCode b = oneHotCode a := by
      have htaken := congrArg (List.take (Fintype.card alpha)) hcat
      simpa [input, oneHotCode_length] using htaken
    have hba : b = a := oneHotCode_injective hcode
    subst b
    rfl
  have hfold := Complexity.Cobham.foldr_table_eq input [] (f a) vals hexists hall
  unfold finiteValueFn
  simpa [vals, finiteValueTable, input, List.foldr_map] using hfold

/-- The stack field for key `k`, following the control field at zero. -/
def stackFieldIndex (tm : Turing.FinTM2) (k : tm.K) : Nat :=
  (Fintype.equivFin tm.K k).val + 1

/-- Push one fixed-width symbol cell onto the selected serialized stack field.
The operation is total and uses the existing fixed-width push/truncate map. -/
def stackFieldPushMap (tm : Turing.FinTM2) (ruler state cell : List Bool)
    (k : tm.K) : List Bool :=
  replaceFixedField ruler state
    (pushCellField cell (fixedFieldAt ruler state (stackFieldIndex tm k)))
    (stackFieldIndex tm k)

theorem stackFieldPushMap_mem (tm : Turing.FinTM2) (k : tm.K)
    (cell : List Bool) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      stackFieldPushMap tm (v 0) (v 1) cell k) := by
  have hread : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)) :=
    (Complexity.Cobham.comp
      (fixedFieldAt_mem (stackFieldIndex tm k))
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have hpush : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      pushCellField cell
        (fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k))) :=
    (Complexity.Cobham.comp (pushCellField_mem cell) (gs := ![hread])).of_eq
      (fun _ => rfl)
  exact (Complexity.Cobham.comp
    (replaceFixedField_mem (stackFieldIndex tm k))
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1, hpush])).of_eq
      (fun _ => rfl)

theorem stackFieldPushMap_correct (tm : Turing.FinTM2)
    (ruler state cell payload : List Bool) (k : tm.K)
    (hread : fixedFieldAt ruler state (stackFieldIndex tm k) = cell ++ payload) :
    stackFieldPushMap tm ruler state cell k =
      replaceFixedField ruler state (cell ++ payload) (stackFieldIndex tm k) := by
  unfold stackFieldPushMap
  rw [hread]
  simp [pushCellField]

/-- Pop one fixed-width cell from a selected stack field and append its
sentinel, preserving a total fixed-width representation. -/
def stackFieldPopMap (tm : Turing.FinTM2) (ruler state sentinel : List Bool)
    (width : Nat) (k : tm.K) : List Bool :=
  replaceFixedField ruler state
    (popCellField width sentinel
      (fixedFieldAt ruler state (stackFieldIndex tm k)))
    (stackFieldIndex tm k)

theorem stackFieldPopMap_mem (tm : Turing.FinTM2) (k : tm.K)
    (width : Nat) (sentinel : List Bool) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      stackFieldPopMap tm (v 0) (v 1) sentinel width k) := by
  have hread : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)) :=
    (Complexity.Cobham.comp
      (fixedFieldAt_mem (stackFieldIndex tm k))
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have hpop : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      popCellField width sentinel
        (fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k))) :=
    (Complexity.Cobham.comp (popCellField_mem width sentinel) (gs := ![hread])).of_eq
      (fun _ => rfl)
  exact (Complexity.Cobham.comp
    (replaceFixedField_mem (stackFieldIndex tm k))
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1, hpop])).of_eq
      (fun _ => rfl)

theorem stackFieldPopMap_correct (tm : Turing.FinTM2)
    (ruler state sentinel cell payload : List Bool) (width : Nat) (k : tm.K)
    (hread : fixedFieldAt ruler state (stackFieldIndex tm k) = cell ++ payload)
    (hwidth : width = cell.length) :
    stackFieldPopMap tm ruler state sentinel width k =
      replaceFixedField ruler state (payload ++ sentinel) (stackFieldIndex tm k) := by
  unfold stackFieldPopMap
  rw [hread, hwidth]
  simp [popCellField]

/-- Data-dependent push: the cell itself is an input field, so finite control
lookup can supply it without an oracle or an assumed transition predicate. -/
def dynamicPushCellField (cell field : List Bool) : List Bool :=
  cell ++ field.take (field.drop cell.length).length

theorem dynamicPushCellField_mem :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      dynamicPushCellField (v 0) (v 1)) := by
  have hdrop : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      (v 1).drop (v 0).length) :=
    Complexity.Cobham.dropFn (Complexity.Cobham.proj 0)
      (Complexity.Cobham.proj 1)
  have htake : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      (v 1).take ((v 1).drop (v 0).length).length) :=
    (Complexity.Cobham.takeFn hdrop (Complexity.Cobham.proj 1)).of_eq
      (fun _ => rfl)
  exact (Complexity.Cobham.appendFn (Complexity.Cobham.proj 0) htake).of_eq
    (fun _ => rfl)

theorem dynamicPushCellField_eq_pushCellField (cell field : List Bool) :
    dynamicPushCellField cell field = pushCellField cell field := by
  simp [dynamicPushCellField, pushCellField, List.length_drop]

def stackFieldDynamicPushMap (tm : Turing.FinTM2)
    (ruler state cell : List Bool) (k : tm.K) : List Bool :=
  replaceFixedField ruler state
    (dynamicPushCellField cell
      (fixedFieldAt ruler state (stackFieldIndex tm k)))
    (stackFieldIndex tm k)

theorem stackFieldDynamicPushMap_mem (tm : Turing.FinTM2) (k : tm.K) :
    Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      stackFieldDynamicPushMap tm (v 0) (v 1) (v 2) k) := by
  have hread : Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)) :=
    (Complexity.Cobham.comp
      (fixedFieldAt_mem (stackFieldIndex tm k))
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have hpush : Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      dynamicPushCellField (v 2)
        (fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k))) :=
    (Complexity.Cobham.comp dynamicPushCellField_mem
      (gs := ![Complexity.Cobham.proj 2, hread])).of_eq (fun _ => rfl)
  exact (Complexity.Cobham.comp
    (replaceFixedField_mem (stackFieldIndex tm k))
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1, hpush])).of_eq
      (fun _ => rfl)

theorem stackFieldDynamicPushMap_correct (tm : Turing.FinTM2)
    (ruler state cell payload : List Bool) (k : tm.K)
    (hread : fixedFieldAt ruler state (stackFieldIndex tm k) = payload) :
    stackFieldDynamicPushMap tm ruler state cell k =
      replaceFixedField ruler state (dynamicPushCellField cell payload)
        (stackFieldIndex tm k) := by
  unfold stackFieldDynamicPushMap
  rw [hread]

/-- Encode the symbol emitted by a push constructor by finite lookup in the
control field. This evaluates the actual `f state` argument. -/
noncomputable def pushCellFromControl (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> tm.Γ k) (ruler state : List Bool) : List Bool := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  exact finiteValueFn
    (fun pair : Prod (Option tm.Λ) tm.σ =>
      stackCellCode tm finiteAlphabets (some (k, f pair.2)))
    (fun _ => fixedFieldAt ruler state 0)

theorem pushCellFromControl_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> tm.Γ k) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      pushCellFromControl tm finiteAlphabets k f (v 0) (v 1)) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  have hread : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) 0) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem 0)
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  exact (Complexity.Cobham.comp
    (finiteValueFn_mem (fun pair : Prod (Option tm.Λ) tm.σ =>
      stackCellCode tm finiteAlphabets (some (k, f pair.2))))
    (gs := ![hread])).of_eq (fun _ => rfl)

theorem pushCellFromControl_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> tm.Γ k)
    (ruler code : List Bool) (controlState : tm.σ)
    (label : Option tm.Λ) (payload : List Bool)
    (hread : fixedFieldAt ruler code 0 =
      oneHotCode (label, controlState) ++ payload) :
    pushCellFromControl tm finiteAlphabets k f ruler code =
      stackCellCode tm finiteAlphabets (some (k, f controlState)) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  unfold pushCellFromControl
  rw [hread]
  exact finiteValueFn_correct
    (fun pair : Prod (Option tm.Λ) tm.σ =>
      stackCellCode tm finiteAlphabets (some (k, f pair.2)))
    (label, controlState) payload
/-- A valid fixed-capacity field implements the actual bounded push when
there is at least one cell of capacity. -/
theorem boundedStackCode_push_dynamic (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (hcapacity : 0 < capacity)
    (symbol : TaggedStackSymbol tm) (stack : List (TaggedStackSymbol tm)) :
    dynamicPushCellField (stackCellCode tm finiteAlphabets (some symbol))
      (boundedStackCode tm finiteAlphabets capacity stack) =
      boundedStackCode tm finiteAlphabets capacity (symbol :: stack) := by
  cases capacity with
  | zero => omega
  | succ capacity =>
      cases stack <;>
        simp [dynamicPushCellField, boundedStackCode_succ_cons,
          boundedStackCode_succ_nil, List.length_drop, stackCellCode_length]

/-- The fixed-field push is the actual `stepAux` push update on every valid
stack encoding with one reserved overflow cell. -/
theorem encoded_push_stack_field_actual (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (hcapacity : 0 < capacity) (k : tm.K)
    (f : σ -> Γ k) (state : σ)
    (ruler encoded : List Bool) (stacks : forall j, List (Γ j))
    (hstack : fixedFieldAt ruler encoded (stackFieldIndex tm k) =
      boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (stacks k))) :
    stackFieldDynamicPushMap tm ruler encoded
      (stackCellCode tm finiteAlphabets (some (k, f state))) k =
    replaceFixedField ruler encoded
      (boundedStackCode tm finiteAlphabets capacity
        (taggedStack tm k ((Function.update stacks k (f state :: stacks k)) k)))
      (stackFieldIndex tm k) := by
  rw [stackFieldDynamicPushMap_correct tm ruler encoded
    (stackCellCode tm finiteAlphabets (some (k, f state)))
    (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (stacks k)))
    k hstack]
  rw [boundedStackCode_push_dynamic tm finiteAlphabets capacity hcapacity
    (k, f state) (taggedStack tm k (stacks k))]
  simp [taggedStack]

/-- Finite code table that decodes one fixed-width stack cell. The all-zero
sentinel and every genuine tagged symbol are both in this carrier. -/
noncomputable def finiteStackCellTable (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : StackCell tm -> List Bool) :
    List (Prod (List Bool) ((Fin 1 -> List Bool) -> List Bool)) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  exact Finset.univ.toList.map (fun cell =>
    (stackCellCode tm finiteAlphabets cell, fun _ => f cell))

def finiteStackCellFn (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : StackCell tm -> List Bool) (v : Fin 1 -> List Bool) : List Bool :=
  (finiteStackCellTable tm finiteAlphabets f).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finiteStackCellFn_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : StackCell tm -> List Bool) :
    Complexity.Cobham (finiteStackCellFn tm finiteAlphabets f) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  unfold finiteStackCellFn finiteStackCellTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 1))
    (Complexity.Cobham.const [])
  intro p hp
  rcases List.mem_map.mp hp with ⟨cell, hcell, rfl⟩
  exact Complexity.Cobham.const (f cell)

theorem finiteStackCellFn_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : StackCell tm -> List Bool) (cell : StackCell tm) (payload : List Bool) :
    finiteStackCellFn tm finiteAlphabets f
      (fun _ => stackCellCode tm finiteAlphabets cell ++ payload) = f cell := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  let input := stackCellCode tm finiteAlphabets cell ++ payload
  let vals := (finiteStackCellTable tm finiteAlphabets f).map
    (fun p => (p.1, p.2 (fun _ => input)))
  have hexists : Exists (fun p : Prod (List Bool) (List Bool) =>
      List.Mem p vals ∧ p.1 <+: input) := by
    refine ⟨(stackCellCode tm finiteAlphabets cell, f cell), ?_, ?_⟩
    · simp [vals, finiteStackCellTable, Finset.mem_toList]
    · exact ⟨payload, rfl⟩
  have hall : forall q, List.Mem q vals -> q.1 <+: input -> q.2 = f cell := by
    intro q hq hprefix
    rcases List.mem_map.mp hq with ⟨p, hp, hqeq⟩
    subst q
    rcases List.mem_map.mp hp with ⟨other, hother, hpeq⟩
    subst p
    rcases hprefix with ⟨suffix, hcat⟩
    have hcode : stackCellCode tm finiteAlphabets other =
        stackCellCode tm finiteAlphabets cell := by
      have htaken := congrArg (List.take (stackCellWidth tm finiteAlphabets)) hcat
      simpa [input, stackCellCode_length] using htaken
    have hsame := stackCellCode_injective tm finiteAlphabets hcode
    subst other
    rfl
  have hfold := Complexity.Cobham.foldr_table_eq input [] (f cell) vals hexists hall
  unfold finiteStackCellFn
  simpa [vals, finiteStackCellTable, input, List.foldr_map] using hfold

def stackTopCellFn (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : StackCell tm -> List Bool) (ruler state : List Bool) : List Bool :=
  finiteStackCellFn tm finiteAlphabets f (fun _ =>
    (fixedFieldAt ruler state (stackFieldIndex tm k)).take
      (stackCellWidth tm finiteAlphabets))

theorem stackTopCellFn_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : StackCell tm -> List Bool) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      stackTopCellFn tm finiteAlphabets k f (v 0) (v 1)) := by
  have hread : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem (stackFieldIndex tm k))
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have htake : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      (fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)).take
        (stackCellWidth tm finiteAlphabets)) :=
    (Complexity.Cobham.takeFn
      (Complexity.Cobham.const (List.replicate
        (stackCellWidth tm finiteAlphabets) false)) hread).of_eq (fun _ => rfl)
  exact (Complexity.Cobham.comp (finiteStackCellFn_mem tm finiteAlphabets f)
    (gs := ![htake])).of_eq (fun _ => rfl)

theorem stackTopCellFn_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : StackCell tm -> List Bool) (ruler state payload : List Bool)
    (cell : StackCell tm)
    (hread : fixedFieldAt ruler state (stackFieldIndex tm k) =
      stackCellCode tm finiteAlphabets cell ++ payload) :
    stackTopCellFn tm finiteAlphabets k f ruler state = f cell := by
  unfold stackTopCellFn
  rw [hread]
  have htake : (stackCellCode tm finiteAlphabets cell ++ payload).take
      (stackCellWidth tm finiteAlphabets) = stackCellCode tm finiteAlphabets cell := by
    simp [stackCellCode_length]
  rw [htake]
  exact finiteStackCellFn_correct tm finiteAlphabets f cell payload

/-- Generic finite lookup whose keys have one common width. -/
noncomputable def finiteKeyValueTable {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool) (f : alpha -> List Bool) :
    List (Prod (List Bool) ((Fin 1 -> List Bool) -> List Bool)) := by
  classical
  exact Finset.univ.toList.map (fun a => (key a, fun _ => f a))

def finiteKeyValueFn {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool) (f : alpha -> List Bool)
    (v : Fin 1 -> List Bool) : List Bool :=
  (finiteKeyValueTable key f).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finiteKeyValueFn_mem {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool) (f : alpha -> List Bool) :
    Complexity.Cobham (finiteKeyValueFn key f) := by
  classical
  unfold finiteKeyValueFn finiteKeyValueTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 1))
    (Complexity.Cobham.const [])
  intro p hp
  rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩
  exact Complexity.Cobham.const (f a)

theorem finiteKeyValueFn_correct {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool) (f : alpha -> List Bool)
    (width : Nat) (hwidth : forall a, (key a).length = width)
    (hinjective : Function.Injective key) (a : alpha) (payload : List Bool) :
    finiteKeyValueFn key f (fun _ => key a ++ payload) = f a := by
  classical
  let input := key a ++ payload
  let vals := (finiteKeyValueTable key f).map
    (fun p => (p.1, p.2 (fun _ => input)))
  have hexists : Exists (fun p : Prod (List Bool) (List Bool) =>
      List.Mem p vals ∧ p.1 <+: input) := by
    refine ⟨(key a, f a), ?_, ?_⟩
    · simp [vals, finiteKeyValueTable, Finset.mem_toList]
    · exact ⟨payload, rfl⟩
  have hall : forall q, List.Mem q vals -> q.1 <+: input -> q.2 = f a := by
    intro q hq hprefix
    rcases List.mem_map.mp hq with ⟨p, hp, hqeq⟩
    subst q
    rcases List.mem_map.mp hp with ⟨b, hb, hpeq⟩
    subst p
    rcases hprefix with ⟨suffix, hcat⟩
    have hcode : key b = key a := by
      have htaken := congrArg (List.take width) hcat
      simpa [input, hwidth] using htaken
    have hsame := hinjective hcode
    subst b
    rfl
  have hfold := Complexity.Cobham.foldr_table_eq input [] (f a) vals hexists hall
  unfold finiteKeyValueFn
  simpa [vals, finiteKeyValueTable, input, List.foldr_map] using hfold

noncomputable def controlCellKey (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (x : (Prod (Option tm.Λ) tm.σ) × StackCell tm) : List Bool :=
  oneHotCode x.1 ++ stackCellCode tm finiteAlphabets x.2

theorem controlCellKey_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (x : (Prod (Option tm.Λ) tm.σ) × StackCell tm) :
    (controlCellKey tm finiteAlphabets x).length =
      Fintype.card (Prod (Option tm.Λ) tm.σ) +
        stackCellWidth tm finiteAlphabets := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  simp [controlCellKey, oneHotCode_length, stackCellCode_length]

theorem controlCellKey_injective (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Function.Injective (controlCellKey tm finiteAlphabets) := by
  classical
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  intro x y h
  rcases x with ⟨controlX, cellX⟩
  rcases y with ⟨controlY, cellY⟩
  have hcontrol : oneHotCode controlX = oneHotCode controlY := by
    have htaken := congrArg
      (List.take (Fintype.card (Prod (Option tm.Λ) tm.σ))) h
    simpa [controlCellKey, oneHotCode_length] using htaken
  have hcell : stackCellCode tm finiteAlphabets cellX =
      stackCellCode tm finiteAlphabets cellY := by
    have hdrop := congrArg
      (List.drop (Fintype.card (Prod (Option tm.Λ) tm.σ))) h
    simpa [controlCellKey, oneHotCode_length] using hdrop
  have hx : controlX = controlY := oneHotCode_injective hcontrol
  have hy : cellX = cellY := stackCellCode_injective tm finiteAlphabets hcell
  cases hx
  cases hy
  rfl

def finiteControlCellFn (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : (Prod (Option tm.Λ) tm.σ) × StackCell tm -> List Bool)
    (v : Fin 1 -> List Bool) : List Bool :=
  finiteKeyValueFn (controlCellKey tm finiteAlphabets) f v

theorem finiteControlCellFn_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : (Prod (Option tm.Λ) tm.σ) × StackCell tm -> List Bool) :
    Complexity.Cobham (finiteControlCellFn tm finiteAlphabets f) :=
  finiteKeyValueFn_mem (controlCellKey tm finiteAlphabets) f

theorem finiteControlCellFn_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (f : (Prod (Option tm.Λ) tm.σ) × StackCell tm -> List Bool)
    (control : Prod (Option tm.Λ) tm.σ) (cell : StackCell tm)
    (payload : List Bool) :
    finiteControlCellFn tm finiteAlphabets f
      (fun _ => controlCellKey tm finiteAlphabets (control, cell) ++ payload) =
      f (control, cell) := by
  unfold finiteControlCellFn
  exact finiteKeyValueFn_correct
    (controlCellKey tm finiteAlphabets) f
    (Fintype.card (Prod (Option tm.Λ) tm.σ) +
      stackCellWidth tm finiteAlphabets)
    (controlCellKey_length tm finiteAlphabets)
    (controlCellKey_injective tm finiteAlphabets)
    (control, cell) payload

def controlTopCellKeyInput (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (ruler state : List Bool) : List Bool :=
  (fixedFieldAt ruler state 0).take
      (Fintype.card (Prod (Option tm.Λ) tm.σ)) ++
    (fixedFieldAt ruler state (stackFieldIndex tm k)).take
      (stackCellWidth tm finiteAlphabets)

theorem controlTopCellKeyInput_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      controlTopCellKeyInput tm finiteAlphabets k (v 0) (v 1)) := by
  have hcontrol : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) 0) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem 0)
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have hstack : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem (stackFieldIndex tm k))
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  have hcontrolTake : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      (fixedFieldAt (v 0) (v 1) 0).take
        (Fintype.card (Prod (Option tm.Λ) tm.σ))) :=
    (Complexity.Cobham.takeFn (Complexity.Cobham.const
      (List.replicate (Fintype.card (Prod (Option tm.Λ) tm.σ)) false)
      ) hcontrol).of_eq (fun _ => rfl)
  have hstackTake : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      (fixedFieldAt (v 0) (v 1) (stackFieldIndex tm k)).take
        (stackCellWidth tm finiteAlphabets)) :=
    (Complexity.Cobham.takeFn (Complexity.Cobham.const
      (List.replicate (stackCellWidth tm finiteAlphabets) false)) hstack).of_eq
        (fun _ => rfl)
  exact (Complexity.Cobham.appendFn hcontrolTake hstackTake).of_eq (fun _ => rfl)

theorem controlTopCellKeyInput_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (ruler state : List Bool)
    (control : Prod (Option tm.Λ) tm.σ) (cell : StackCell tm)
    (controlPayload cellPayload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ controlPayload)
    (hcell : fixedFieldAt ruler state (stackFieldIndex tm k) =
      stackCellCode tm finiteAlphabets cell ++ cellPayload) :
    controlTopCellKeyInput tm finiteAlphabets k ruler state =
      controlCellKey tm finiteAlphabets (control, cell) := by
  unfold controlTopCellKeyInput controlCellKey
  rw [hcontrol, hcell]
  simp [oneHotCode_length, stackCellCode_length]

def controlTopCellFn (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K)
    (f : (Prod (Option tm.Λ) tm.σ) × StackCell tm -> List Bool)
    (ruler state : List Bool) : List Bool :=
  finiteControlCellFn tm finiteAlphabets f
    (fun _ => controlTopCellKeyInput tm finiteAlphabets k ruler state)

theorem controlTopCellFn_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K)
    (f : (Prod (Option tm.Λ) tm.σ) × StackCell tm -> List Bool) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      controlTopCellFn tm finiteAlphabets k f (v 0) (v 1)) := by
  have hkey : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      controlTopCellKeyInput tm finiteAlphabets k (v 0) (v 1)) :=
    controlTopCellKeyInput_mem tm finiteAlphabets k
  exact (Complexity.Cobham.comp (finiteControlCellFn_mem tm finiteAlphabets f)
    (gs := ![hkey])).of_eq (fun _ => rfl)

theorem controlTopCellFn_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K)
    (f : (Prod (Option tm.Λ) tm.σ) × StackCell tm -> List Bool)
    (ruler state : List Bool) (control : Prod (Option tm.Λ) tm.σ)
    (cell : StackCell tm) (controlPayload cellPayload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ controlPayload)
    (hcell : fixedFieldAt ruler state (stackFieldIndex tm k) =
      stackCellCode tm finiteAlphabets cell ++ cellPayload) :
    controlTopCellFn tm finiteAlphabets k f ruler state = f (control, cell) := by
  unfold controlTopCellFn
  rw [controlTopCellKeyInput_correct tm finiteAlphabets k ruler state control cell
    controlPayload cellPayload hcontrol hcell]
  simpa using finiteControlCellFn_correct tm finiteAlphabets f control cell []

/-- Decode the selected physical stack top from the common tagged-cell code.
Malformed tags are totalized as `none`; valid fields carry the selected key. -/
def decodeStackCellAt (tm : Turing.FinTM2) (k : tm.K)
    (cell : StackCell tm) : Option (tm.Γ k) :=
  match cell with
  | none => none
  | some symbol =>
      if h : symbol.1 = k then some (h ▸ symbol.2) else none

@[simp] theorem decodeStackCellAt_none (tm : Turing.FinTM2) (k : tm.K) :
    decodeStackCellAt tm k none = none := rfl

@[simp] theorem decodeStackCellAt_some (tm : Turing.FinTM2) (k : tm.K)
    (symbol : tm.Γ k) :
    decodeStackCellAt tm k (some ⟨k, symbol⟩) = some symbol := by
  simp [decodeStackCellAt]

noncomputable def peekControlFieldMap (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (ruler state : List Bool) : List Bool :=
  replaceFixedField ruler state
    (controlTopCellFn tm finiteAlphabets k
      (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
      ruler state) 0

theorem peekControlFieldMap_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      peekControlFieldMap tm finiteAlphabets k f (v 0) (v 1)) := by
  have hcontrolCell : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      controlTopCellFn tm finiteAlphabets k
        (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
        (v 0) (v 1)) :=
    controlTopCellFn_mem tm finiteAlphabets k
      (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
  exact (Complexity.Cobham.comp (replaceFixedField_mem 0)
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1, hcontrolCell])
    ).of_eq (fun _ => rfl)

theorem peekControlFieldMap_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (ruler state : List Bool) (control : Prod (Option tm.Λ) tm.σ)
    (cell : StackCell tm) (controlPayload cellPayload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ controlPayload)
    (hcell : fixedFieldAt ruler state (stackFieldIndex tm k) =
      stackCellCode tm finiteAlphabets cell ++ cellPayload) :
    peekControlFieldMap tm finiteAlphabets k f ruler state =
      replaceFixedField ruler state
        (oneHotCode (control.1, f control.2 (decodeStackCellAt tm k cell))) 0 := by
  unfold peekControlFieldMap
  rw [controlTopCellFn_correct tm finiteAlphabets k
    (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
    ruler state control cell controlPayload cellPayload hcontrol hcell]

theorem peekControlFieldMap_actual_top (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (control : Prod (Option tm.Λ) tm.σ) (symbol : tm.Γ k) :
    oneHotCode (control.1,
      f control.2 (decodeStackCellAt tm k (some ⟨k, symbol⟩))) =
    oneHotCode (control.1, f control.2 (some symbol)) := by
  simp [decodeStackCellAt]

/-- Pop combines the actual continuation-state update from the decoded top
cell with the fixed-field stack shift and appended sentinel. -/
def popFieldsMap (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (ruler state : List Bool) : List Bool :=
  replaceFixedField ruler
    (stackFieldPopMap tm ruler state
      (stackCellCode tm finiteAlphabets none)
      (stackCellWidth tm finiteAlphabets) k)
    (controlTopCellFn tm finiteAlphabets k
      (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
      ruler state) 0

theorem popFieldsMap_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      popFieldsMap tm finiteAlphabets k f (v 0) (v 1)) := by
  have hstack : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      stackFieldPopMap tm (v 0) (v 1)
        (stackCellCode tm finiteAlphabets none)
        (stackCellWidth tm finiteAlphabets) k) :=
    stackFieldPopMap_mem tm k (stackCellWidth tm finiteAlphabets)
      (stackCellCode tm finiteAlphabets none)
  have hcontrol : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      controlTopCellFn tm finiteAlphabets k
        (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
        (v 0) (v 1)) :=
    controlTopCellFn_mem tm finiteAlphabets k
      (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
  have hmiddle : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      replaceFixedField (v 0)
        (stackFieldPopMap tm (v 0) (v 1)
          (stackCellCode tm finiteAlphabets none)
          (stackCellWidth tm finiteAlphabets) k)
        (controlTopCellFn tm finiteAlphabets k
          (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
          (v 0) (v 1)) 0) :=
    (Complexity.Cobham.comp (replaceFixedField_mem 0)
      (gs := ![Complexity.Cobham.proj 0, hstack, hcontrol])).of_eq (fun _ => rfl)
  exact hmiddle.of_eq (fun _ => rfl)

theorem popFieldsMap_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (ruler state : List Bool) (control : Prod (Option tm.Λ) tm.σ)
    (cell : StackCell tm) (controlPayload cellPayload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ controlPayload)
    (hcell : fixedFieldAt ruler state (stackFieldIndex tm k) =
      stackCellCode tm finiteAlphabets cell ++ cellPayload) :
    popFieldsMap tm finiteAlphabets k f ruler state =
      replaceFixedField ruler
        (replaceFixedField ruler state (cellPayload ++
          stackCellCode tm finiteAlphabets none) (stackFieldIndex tm k))
        (oneHotCode (control.1, f control.2 (decodeStackCellAt tm k cell))) 0 := by
  unfold popFieldsMap
  rw [stackFieldPopMap_correct tm ruler state
    (stackCellCode tm finiteAlphabets none) (stackCellCode tm finiteAlphabets cell)
    cellPayload (stackCellWidth tm finiteAlphabets) k hcell
    (stackCellCode_length tm finiteAlphabets cell).symm]
  rw [controlTopCellFn_correct tm finiteAlphabets k
    (fun x => oneHotCode (x.1.1, f x.1.2 (decodeStackCellAt tm k x.2)))
    ruler state control cell controlPayload cellPayload hcontrol hcell]

theorem boundedStackCode_succ_fit (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stack : List (TaggedStackSymbol tm))
    (hfit : stack.length <= capacity) :
    boundedStackCode tm finiteAlphabets (capacity + 1) stack =
      boundedStackCode tm finiteAlphabets capacity stack ++
        stackCellCode tm finiteAlphabets none := by
  induction capacity generalizing stack with
  | zero =>
      have hnil : stack = [] := by
        have hlen : stack.length = 0 := by omega
        exact List.length_eq_zero.mp hlen
      subst stack
      simp [boundedStackCode_succ_nil]
  | succ capacity ih =>
      cases stack with
      | nil => simp [boundedStackCode_succ_nil]
      | cons symbol rest =>
          have hrest : rest.length <= capacity := by simp at hfit; omega
          simp [boundedStackCode_succ_cons, ih rest hrest, List.append_assoc]

theorem boundedStackCode_pop_field_actual (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (hcapacity : 0 < capacity)
    (symbol : TaggedStackSymbol tm) (stack : List (TaggedStackSymbol tm))
    (hfit : stack.length < capacity) :
    popCellField (stackCellWidth tm finiteAlphabets)
      (stackCellCode tm finiteAlphabets none)
      (boundedStackCode tm finiteAlphabets capacity (symbol :: stack)) =
    boundedStackCode tm finiteAlphabets capacity stack := by
  cases capacity with
  | zero => omega
  | succ capacity =>
      have hrest : stack.length <= capacity := by omega
      rw [boundedStackCode_succ_cons]
      unfold popCellField
      simp [stackCellCode_length, List.drop_append]
      rw [boundedStackCode_succ_fit tm finiteAlphabets capacity stack hrest]

/-- The actual `statementPushBound` invariant supplies enough capacity at
 every nested `.push` prefix, including the cell currently being inserted. -/
theorem statementPushSlack_after_push (tm : Turing.FinTM2)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (k : tm.K) (f : tm.σ -> tm.Γ k) (state : tm.σ)
    (stacks : forall j, List (tm.Γ j)) (capacity : Nat)
    (h : forall j, (stacks j).length +
      Runtime.statementPushBound (Turing.TM2.Stmt.push k f next) <= capacity) :
    forall j, (Function.update stacks k (f state :: stacks k) j).length +
      Runtime.statementPushBound next <= capacity := by
  intro j
  by_cases hj : j = k
  · subst j
    have hk := h k
    simp [Runtime.statementPushBound] at hk
    simp [Function.update_same]
    omega
  · have hother := h j
    simp [Runtime.statementPushBound] at hother
    simp [Function.update_of_ne hj]
    omega

theorem statementPushSlack_after_pop (tm : Turing.FinTM2)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (state : tm.σ) (stacks : forall j, List (tm.Γ j))
    (capacity : Nat)
    (h : forall j, (stacks j).length +
      Runtime.statementPushBound (Turing.TM2.Stmt.pop k f next) <= capacity) :
    forall j, (Function.update stacks k (stacks k).tail j).length +
      Runtime.statementPushBound next <= capacity := by
  intro j
  by_cases hj : j = k
  · subst j
    have hk := h k
    simp [Runtime.statementPushBound] at hk
    simp [Function.update_same]
    have htail : (stacks k).tail.length <= (stacks k).length := by
      simp [List.length_tail]
    omega
  · have hother := h j
    simp [Runtime.statementPushBound] at hother
    simpa [Function.update_of_ne hj, Runtime.statementPushBound] using hother

theorem statementPushSlack_after_peek (tm : Turing.FinTM2)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (k : tm.K) (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (stacks : forall j, List (tm.Γ j)) (capacity : Nat)
    (h : forall j, (stacks j).length +
      Runtime.statementPushBound (Turing.TM2.Stmt.peek k f next) <= capacity) :
    forall j, (stacks j).length + Runtime.statementPushBound next <= capacity := by
  intro j
  have hj := h j
  simpa [Runtime.statementPushBound] using hj

theorem statementPushSlack_after_load (tm : Turing.FinTM2)
    (next : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (f : tm.σ -> tm.σ) (stacks : forall j, List (tm.Γ j))
    (capacity : Nat)
    (h : forall j, (stacks j).length +
      Runtime.statementPushBound (Turing.TM2.Stmt.load f next) <= capacity) :
    forall j, (stacks j).length + Runtime.statementPushBound next <= capacity := by
  intro j
  have hj := h j
  simpa [Runtime.statementPushBound] using hj

theorem statementPushSlack_after_branch (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool)
    (yes no : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (stacks : forall j, List (tm.Γ j)) (capacity : Nat)
    (h : forall j, (stacks j).length +
      Runtime.statementPushBound (Turing.TM2.Stmt.branch condition yes no) <= capacity) :
    (forall j, (stacks j).length + Runtime.statementPushBound yes <= capacity) ∧
    (forall j, (stacks j).length + Runtime.statementPushBound no <= capacity) := by
  constructor <;> intro j
  · have hj := h j
    simp [Runtime.statementPushBound] at hj
    omega
  · have hj := h j
    simp [Runtime.statementPushBound] at hj
    omega

theorem popFieldsMap_actual_nonempty (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (hcapacity : 0 < capacity) (k : tm.K)
    (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (ruler state : List Bool) (control : Prod (Option tm.Λ) tm.σ)
    (controlPayload : List Bool) (symbol : tm.Γ k)
    (stack : List (tm.Γ k))
    (hfit : stack.length < capacity)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ controlPayload)
    (hfield : fixedFieldAt ruler state (stackFieldIndex tm k) =
      boundedStackCode tm finiteAlphabets capacity
        (taggedStack tm k (symbol :: stack))) :
    popFieldsMap tm finiteAlphabets k f ruler state =
      replaceFixedField ruler
        (replaceFixedField ruler state
          (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack))
          (stackFieldIndex tm k))
        (oneHotCode (control.1, f control.2 (some symbol))) 0 := by
  cases capacity with
  | zero => omega
  | succ capacity =>
      have hcell : fixedFieldAt ruler state (stackFieldIndex tm k) =
          stackCellCode tm finiteAlphabets (some ⟨k, symbol⟩) ++
            boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack) := by
        simpa [taggedStack] using hfield
      have hpop := popFieldsMap_correct tm finiteAlphabets k f ruler state control
        (some ⟨k, symbol⟩)
        controlPayload (boundedStackCode tm finiteAlphabets capacity
          (taggedStack tm k stack)) hcontrol hcell
      have hlength : (taggedStack tm k stack).length <= capacity := by
        simp [taggedStack]
        omega
      have htail := boundedStackCode_succ_fit tm finiteAlphabets capacity
        (taggedStack tm k stack) hlength
      simpa [decodeStackCellAt, htail] using hpop

theorem popFieldsMap_actual_empty (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (hcapacity : 0 < capacity) (k : tm.K)
    (f : tm.σ -> Option (tm.Γ k) -> tm.σ)
    (ruler state : List Bool) (control : Prod (Option tm.Λ) tm.σ)
    (controlPayload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ controlPayload)
    (hfield : fixedFieldAt ruler state (stackFieldIndex tm k) =
      boundedStackCode tm finiteAlphabets capacity (taggedStack tm k [])) :
    popFieldsMap tm finiteAlphabets k f ruler state =
      replaceFixedField ruler
        (replaceFixedField ruler state
          (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k []))
          (stackFieldIndex tm k))
        (oneHotCode (control.1, f control.2 none)) 0 := by
  cases capacity with
  | zero => omega
  | succ capacity =>
      have hcell : fixedFieldAt ruler state (stackFieldIndex tm k) =
          stackCellCode tm finiteAlphabets none ++
            boundedStackCode tm finiteAlphabets capacity (taggedStack tm k []) := by
        simpa [taggedStack] using hfield
      have hpop := popFieldsMap_correct tm finiteAlphabets k f ruler state control
        none controlPayload
        (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k []))
        hcontrol hcell
      have htail : (taggedStack tm k []).length <= capacity := by simp [taggedStack]
      have hbound := boundedStackCode_succ_fit tm finiteAlphabets capacity
        (taggedStack tm k []) htail
      simpa [decodeStackCellAt, hbound] using hpop

theorem stepAux_result_stack_fits (tm : Turing.FinTM2)
    (stmt : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (state : tm.σ) (stacks : forall k, List (tm.Γ k))
    (capacity : Nat)
    (hslack : forall k, (stacks k).length + Runtime.statementPushBound stmt <= capacity) :
    forall k, ((Turing.TM2.stepAux stmt state stacks).stk k).length <= capacity := by
  intro k
  have hstep := Runtime.stepAuxStackLength stmt state stacks k
  have hk := hslack k
  omega

theorem programStepAux_result_stack_fits (tm : Turing.FinTM2)
    (label : tm.Λ) (state : tm.σ)
    (stacks : forall k, List (tm.Γ k)) (capacity : Nat)
    (hslack : forall k, (stacks k).length + Runtime.programPushBound tm <= capacity) :
    forall k, ((Turing.TM2.stepAux (tm.m label) state stacks).stk k).length <= capacity := by
  apply stepAux_result_stack_fits tm (tm.m label) state stacks capacity
  intro k
  have hbound := Runtime.statement_le_programPushBound tm label
  have hk := hslack k
  omega

/-- A finite Cobham case split on a one-bit first input. Both branches receive
all remaining vector inputs unchanged. -/
def finiteTwoWayTable {n : Nat}
    (yes no : (Fin n -> List Bool) -> List Bool) :
    List (Prod (List Bool) ((Fin (n + 1) -> List Bool) -> List Bool)) :=
  [([false], fun v => no (fun i => v i.succ)),
   ([true], fun v => yes (fun i => v i.succ))]

def finiteTwoWayFn {n : Nat}
    (yes no : (Fin n -> List Bool) -> List Bool)
    (v : Fin (n + 1) -> List Bool) : List Bool :=
  (finiteTwoWayTable yes no).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finiteTwoWayFn_mem {n : Nat}
    (yes no : (Fin n -> List Bool) -> List Bool)
    (hyes : Complexity.Cobham yes) (hno : Complexity.Cobham no) :
    Complexity.Cobham (finiteTwoWayFn yes no) := by
  have hyes' : Complexity.Cobham (fun v : Fin (n + 1) -> List Bool =>
      yes (fun i => v i.succ)) :=
    (Complexity.Cobham.comp hyes
      (gs := fun i => Complexity.Cobham.proj i.succ)).of_eq (fun _ => rfl)
  have hno' : Complexity.Cobham (fun v : Fin (n + 1) -> List Bool =>
      no (fun i => v i.succ)) :=
    (Complexity.Cobham.comp hno
      (gs := fun i => Complexity.Cobham.proj i.succ)).of_eq (fun _ => rfl)
  unfold finiteTwoWayFn
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj 0) (Complexity.Cobham.const [])
  intro p hp
  simp [finiteTwoWayTable] at hp
  rcases hp with h | h
  · cases h
    exact hno'
  · cases h
    exact hyes'

theorem finiteTwoWayFn_true {n : Nat}
    (yes no : (Fin n -> List Bool) -> List Bool)
    (v : Fin (n + 1) -> List Bool) (hbit : v 0 = [true]) :
    finiteTwoWayFn yes no v = yes (fun i => v i.succ) := by
  unfold finiteTwoWayFn
  simp [finiteTwoWayTable, hbit]

theorem finiteTwoWayFn_false {n : Nat}
    (yes no : (Fin n -> List Bool) -> List Bool)
    (v : Fin (n + 1) -> List Bool) (hbit : v 0 = [false]) :
    finiteTwoWayFn yes no v = no (fun i => v i.succ) := by
  unfold finiteTwoWayFn
  simp [finiteTwoWayTable, hbit]

noncomputable def branchConditionFromControl (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool) (ruler state : List Bool) : List Bool :=
  finiteValueFn (fun pair : Prod (Option tm.Λ) tm.σ =>
    [condition pair.2]) (fun _ => fixedFieldAt ruler state 0)

theorem branchConditionFromControl_mem (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      branchConditionFromControl tm condition (v 0) (v 1)) := by
  have hread : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) 0) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem 0)
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  exact (Complexity.Cobham.comp
    (finiteValueFn_mem (fun pair : Prod (Option tm.Λ) tm.σ =>
      [condition pair.2])) (gs := ![hread])).of_eq (fun _ => rfl)

theorem branchConditionFromControl_correct (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool) (ruler state : List Bool)
    (control : Prod (Option tm.Λ) tm.σ) (payload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ payload) :
    branchConditionFromControl tm condition ruler state = [condition control.2] := by
  unfold branchConditionFromControl
  rw [hcontrol]
  exact finiteValueFn_correct (fun pair : Prod (Option tm.Λ) tm.σ =>
    [condition pair.2]) control payload

def branchFieldMap (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool)
    (yes no : (Fin 2 -> List Bool) -> List Bool)
    (ruler state : List Bool) : List Bool :=
  finiteTwoWayFn yes no
    ![branchConditionFromControl tm condition ruler state, ruler, state]

theorem branchFieldMap_mem (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool)
    (yes no : (Fin 2 -> List Bool) -> List Bool)
    (hyes : Complexity.Cobham yes) (hno : Complexity.Cobham no) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      branchFieldMap tm condition yes no (v 0) (v 1)) := by
  have hcondition : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      branchConditionFromControl tm condition (v 0) (v 1)) :=
    branchConditionFromControl_mem tm condition
  exact (Complexity.Cobham.comp (finiteTwoWayFn_mem yes no hyes hno)
    (gs := ![hcondition, Complexity.Cobham.proj 0, Complexity.Cobham.proj 1]))
    .of_eq (fun _ => rfl)

theorem branchFieldMap_correct (tm : Turing.FinTM2)
    (condition : tm.σ -> Bool)
    (yes no : (Fin 2 -> List Bool) -> List Bool)
    (ruler state : List Bool) (control : Prod (Option tm.Λ) tm.σ)
    (payload : List Bool)
    (hcontrol : fixedFieldAt ruler state 0 = oneHotCode control ++ payload) :
    branchFieldMap tm condition yes no ruler state =
      if condition control.2 then yes ![ruler, state] else no ![ruler, state] := by
  unfold branchFieldMap
  rw [branchConditionFromControl_correct tm condition ruler state control payload hcontrol]
  by_cases hcondition : condition control.2
  · simp [finiteTwoWayFn, finiteTwoWayTable, hcondition]
  · simp [finiteTwoWayFn, finiteTwoWayTable, hcondition]
def pushFieldsMap (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> tm.Γ k) (ruler state : List Bool) : List Bool :=
  stackFieldDynamicPushMap tm ruler state
    (pushCellFromControl tm finiteAlphabets k f ruler state) k

theorem pushFieldsMap_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (f : tm.σ -> tm.Γ k) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      pushFieldsMap tm finiteAlphabets k f (v 0) (v 1)) := by
  have hcell : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      pushCellFromControl tm finiteAlphabets k f (v 0) (v 1)) :=
    pushCellFromControl_mem tm finiteAlphabets k f
  exact (Complexity.Cobham.comp (stackFieldDynamicPushMap_mem tm k)
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1, hcell])).of_eq
      (fun _ => rfl)

theorem controlFieldMap_mem_twoInput (tm : Turing.FinTM2)
    (f : Prod (Option tm.Λ) tm.σ -> Prod (Option tm.Λ) tm.σ) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      controlFieldMap tm (v 0) (v 1) f) := by
  exact (Complexity.Cobham.comp (controlFieldMap_mem tm f)
    (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1,
      Complexity.Cobham.const []])).of_eq (fun _ => rfl)

/-- Structural compiler for the complete actual `Stmt` tree. Its output is a
composition of fixed-field Cobham maps; correctness against the full
`fixedConfigurationCode (stepAux ...)` is a separate theorem obligation. -/
noncomputable def stmtFieldMap (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ ->
      (Fin 2 -> List Bool) -> List Bool
  | .push k f next => fun v =>
      stmtFieldMap tm finiteAlphabets next
        ![v 0, pushFieldsMap tm finiteAlphabets k f (v 0) (v 1)]
  | .peek k f next => fun v =>
      stmtFieldMap tm finiteAlphabets next
        ![v 0, peekControlFieldMap tm finiteAlphabets k f (v 0) (v 1)]
  | .pop k f next => fun v =>
      stmtFieldMap tm finiteAlphabets next
        ![v 0, popFieldsMap tm finiteAlphabets k f (v 0) (v 1)]
  | .load f next => fun v =>
      stmtFieldMap tm finiteAlphabets next
        ![v 0, controlFieldMap tm (v 0) (v 1)
          (fun pair => (pair.1, f pair.2))]
  | .branch condition yes no => fun v =>
      branchFieldMap tm condition
        (stmtFieldMap tm finiteAlphabets yes)
        (stmtFieldMap tm finiteAlphabets no) (v 0) (v 1)
  | .goto target => fun v =>
      controlFieldMap tm (v 0) (v 1)
        (fun pair => (some (target pair.2), pair.2))
  | .halt => fun v =>
      controlFieldMap tm (v 0) (v 1)
        (fun pair => (none, pair.2))

theorem stmtFieldMap_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (stmt : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      stmtFieldMap tm finiteAlphabets stmt v) := by
  induction stmt with
  | push k f next ih =>
      have hpush : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
          pushFieldsMap tm finiteAlphabets k f (v 0) (v 1)) :=
        pushFieldsMap_mem tm finiteAlphabets k f
      exact (Complexity.Cobham.comp ih
        (gs := ![Complexity.Cobham.proj 0, hpush])).of_eq (fun _ => rfl)
  | peek k f next ih =>
      exact (Complexity.Cobham.comp ih
        (gs := ![Complexity.Cobham.proj 0,
          peekControlFieldMap_mem tm finiteAlphabets k f])).of_eq (fun _ => rfl)
  | pop k f next ih =>
      exact (Complexity.Cobham.comp ih
        (gs := ![Complexity.Cobham.proj 0,
          popFieldsMap_mem tm finiteAlphabets k f])).of_eq (fun _ => rfl)
  | load f next ih =>
      exact (Complexity.Cobham.comp ih
        (gs := ![Complexity.Cobham.proj 0,
          (controlFieldMap_mem_twoInput tm (fun pair => (pair.1, f pair.2)))])).of_eq
            (fun _ => rfl)
  | branch condition yes no ihYes ihNo =>
      exact branchFieldMap_mem tm condition
        (stmtFieldMap tm finiteAlphabets yes)
        (stmtFieldMap tm finiteAlphabets no) ihYes ihNo
  | goto target =>
      exact controlFieldMap_mem_twoInput tm
        (fun pair => (some (target pair.2), pair.2))
  | halt =>
      exact controlFieldMap_mem_twoInput tm (fun pair => (none, pair.2))

/-- On a canonical serialized configuration, a finite control-field map is
exactly the canonical whole-code update of the actual TM2 register/label. -/
theorem controlFieldMap_canonical (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg)
    (f : Prod (Option tm.Λ) tm.σ -> Prod (Option tm.Λ) tm.σ)
    (hcontrolWidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      (fixedFieldRuler tm finiteAlphabets capacity).length) :
    controlFieldMap tm (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) f =
    fixedConfigurationCode tm finiteAlphabets capacity
      { cfg with l := (f (cfg.l, cfg.var)).1, var := (f (cfg.l, cfg.var)).2 } := by
  let ruler := fixedFieldRuler tm finiteAlphabets capacity
  let code := fixedConfigurationCode tm finiteAlphabets capacity cfg
  let control : Prod (Option tm.Λ) tm.σ := (cfg.l, cfg.var)
  have hlength : (oneHotCode control).length <= ruler.length := by
    simpa [control, ruler, oneHotCode_length] using hcontrolWidth
  have hread : fixedFieldAt ruler code 0 =
      oneHotCode control ++ List.replicate (ruler.length - (oneHotCode control).length) false := by
    rw [show ruler = fixedFieldRuler tm finiteAlphabets capacity by rfl,
      show code = fixedConfigurationCode tm finiteAlphabets capacity cfg by rfl]
    rw [fixedFieldAt_controlBlock]
    rw [controlBlock]
    exact Complexity.Cobham.padTo_eq_append ruler (oneHotCode control) hlength
  have hmap := controlFieldMap_correct tm ruler code f control
    (List.replicate (ruler.length - (oneHotCode control).length) false) hread
  rw [hmap]
  rw [Complexity.Cobham.padTo_append_replicate]
  symm
  exact fixedConfigurationCode_controlUpdate tm finiteAlphabets capacity cfg
    (f control).1 (f control).2

/-- Finite-key dispatch preserving two payload inputs for the selected branch.
The finite table selects a fixed constructor by its common-width key, while the
branch function still receives the complete ruler and configuration code. -/
noncomputable def finiteKeyDispatchTable {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool)
    (f : alpha -> (Fin 2 -> List Bool) -> List Bool) :
    List (Prod (List Bool) ((Fin 3 -> List Bool) -> List Bool)) := by
  classical
  exact Finset.univ.toList.map (fun a =>
    (key a, fun v => f a ![v 1, v 2]))

def finiteKeyDispatchFn {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool)
    (f : alpha -> (Fin 2 -> List Bool) -> List Bool)
    (v : Fin 3 -> List Bool) : List Bool :=
  (finiteKeyDispatchTable key f).foldr (fun p acc =>
    Complexity.caseBit₀ (Complexity.matchPrefix p.1 (v 0)) (p.2 v) acc) []

theorem finiteKeyDispatchFn_mem {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool)
    (f : alpha -> (Fin 2 -> List Bool) -> List Bool)
    (hf : forall a, Complexity.Cobham (f a)) :
    Complexity.Cobham (finiteKeyDispatchFn key f) := by
  classical
  unfold finiteKeyDispatchFn finiteKeyDispatchTable
  apply Complexity.Cobham.tableFn
    (Complexity.Cobham.proj (0 : Fin 3)) (Complexity.Cobham.const [])
  intro p hp
  rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩
  have hbranch : Complexity.Cobham (fun v : Fin 3 -> List Bool => f a ![v 1, v 2]) :=
    (Complexity.Cobham.comp (hf a)
      (gs := ![Complexity.Cobham.proj 1, Complexity.Cobham.proj 2])).of_eq
        (fun _ => rfl)
  exact hbranch

theorem finiteKeyDispatchFn_correct {alpha : Type} [Fintype alpha]
    (key : alpha -> List Bool)
    (f : alpha -> (Fin 2 -> List Bool) -> List Bool)
    (width : Nat) (hwidth : forall a, (key a).length = width)
    (hinjective : Function.Injective key) (a : alpha) (payload x y : List Bool) :
    finiteKeyDispatchFn key f ![key a ++ payload, x, y] = f a ![x, y] := by
  have htable : finiteKeyDispatchFn key f ![key a ++ payload, x, y] =
      finiteKeyValueFn key (fun b => f b ![x, y]) (fun _ => key a ++ payload) := by
    rfl
  rw [htable]
  exact finiteKeyValueFn_correct key (fun b => f b ![x, y]) width hwidth hinjective
    a payload

/-- Dispatch the actual finite TM2 program by the encoded optional label and
register. A halted (`none`) control keeps the serialized configuration fixed. -/
noncomputable def programStatementDispatch (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (ruler state : List Bool) : List Bool :=
  finiteKeyDispatchFn (fun control : Prod (Option tm.Λ) tm.σ => oneHotCode control)
    (fun control v =>
      match control.1 with
      | none => v 1
      | some label => stmtFieldMap tm finiteAlphabets (tm.m label) v)
    ![fixedFieldAt ruler state 0, ruler, state]

theorem programStatementDispatch_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      programStatementDispatch tm finiteAlphabets (v 0) (v 1)) := by
  have hbranches : forall control : Prod (Option tm.Λ) tm.σ,
      Complexity.Cobham (fun v : Fin 2 -> List Bool =>
        match control.1 with
        | none => v 1
        | some label => stmtFieldMap tm finiteAlphabets (tm.m label) v) := by
    intro control
    cases hlabel : control.1 with
    | none => simp [hlabel]; exact Complexity.Cobham.proj 1
    | some label => simp [hlabel]; exact stmtFieldMap_mem tm finiteAlphabets (tm.m label)
  have hdispatch := finiteKeyDispatchFn_mem
    (fun control : Prod (Option tm.Λ) tm.σ => oneHotCode control)
    (fun control v =>
      match control.1 with
      | none => v 1
      | some label => stmtFieldMap tm finiteAlphabets (tm.m label)) hbranches
  have hread : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      fixedFieldAt (v 0) (v 1) 0) :=
    (Complexity.Cobham.comp (fixedFieldAt_mem 0)
      (gs := ![Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
        (fun _ => rfl)
  exact (Complexity.Cobham.comp hdispatch
    (gs := ![hread, Complexity.Cobham.proj 0, Complexity.Cobham.proj 1])).of_eq
      (fun _ => rfl)

theorem programStatementDispatch_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg)
    (hcontrolWidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      (fixedFieldRuler tm finiteAlphabets capacity).length) :
    programStatementDispatch tm finiteAlphabets
      (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) =
      match cfg.l with
      | none => fixedConfigurationCode tm finiteAlphabets capacity cfg
      | some label => stmtFieldMap tm finiteAlphabets (tm.m label)
          ![fixedFieldRuler tm finiteAlphabets capacity,
            fixedConfigurationCode tm finiteAlphabets capacity cfg] := by
  let ruler := fixedFieldRuler tm finiteAlphabets capacity
  let code := fixedConfigurationCode tm finiteAlphabets capacity cfg
  let control : Prod (Option tm.Λ) tm.σ := (cfg.l, cfg.var)
  have hlength : (oneHotCode control).length <= ruler.length := by
    simpa [control, ruler, oneHotCode_length] using hcontrolWidth
  have hread : fixedFieldAt ruler code 0 =
      oneHotCode control ++ List.replicate (ruler.length - (oneHotCode control).length) false := by
    rw [show ruler = fixedFieldRuler tm finiteAlphabets capacity by rfl,
      show code = fixedConfigurationCode tm finiteAlphabets capacity cfg by rfl]
    rw [fixedFieldAt_controlBlock, controlBlock]
    exact Complexity.Cobham.padTo_eq_append ruler (oneHotCode control) hlength
  have hdispatch := finiteKeyDispatchFn_correct
    (fun c : Prod (Option tm.Λ) tm.σ => oneHotCode c)
    (fun c v =>
      match c.1 with
      | none => v 1
      | some label => stmtFieldMap tm finiteAlphabets (tm.m label) v)
    (Fintype.card (Prod (Option tm.Λ) tm.σ))
    (fun c => oneHotCode_length c)
    oneHotCode_injective control
    (List.replicate (ruler.length - (oneHotCode control).length) false) ruler code
  unfold programStatementDispatch
  rw [hread]
  simpa [control, ruler, code] using hdispatch

theorem list_set_eq_take_append_cons_drop {α : Type} (xs : List α)
    (i : Nat) (value : α) (hi : i < xs.length) :
    xs.set i value = xs.take i ++ value :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < tail.length := by simpa using hi
          have hrec := ih i value hi'
          simpa [List.set] using congrArg (fun rest : List α => head :: rest) hrec

/-- Updating one physical stack in a canonical configuration is exactly the
fixed-field replacement used by the Cobham code. -/
theorem fixedConfigurationCode_stackUpdate (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) (k : tm.K) (stack : List (tm.Γ k)) :
    fixedConfigurationCode tm finiteAlphabets capacity
      { cfg with stk := Function.update cfg.stk k stack } =
      replaceFixedField (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity cfg)
        (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack))
        (stackFieldIndex tm k) := by
  let i : Fin (Fintype.card tm.K + 1) := Fin.succ (Fintype.equivFin tm.K k)
  have hfields :
      List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity
        { cfg with stk := Function.update cfg.stk k stack }) =
      (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity cfg)).take i.val ++
        Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
          (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack)) ::
        (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity cfg)).drop (i.val + 1) := by
    rw [fixedConfigurationFields_stackUpdate]
    rw [list_ofFn_update]
    exact list_set_eq_take_append_cons_drop
      (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity cfg)) i.val
      (Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
        (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack))) (by simp)
  have hcode := fixedConfigurationCode_replaceField tm finiteAlphabets capacity cfg
    { cfg with stk := Function.update cfg.stk k stack } i
    (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack)) hfields
  simpa [i, stackFieldIndex] using hcode

theorem fixedConfigurationCode_controlSplit (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg)
    (hwidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      (fixedFieldRuler tm finiteAlphabets capacity).length) :
    fixedFieldAt (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) 0 =
      oneHotCode (cfg.l, cfg.var) ++
        List.replicate ((fixedFieldRuler tm finiteAlphabets capacity).length -
          (oneHotCode (cfg.l, cfg.var)).length) false := by
  rw [fixedFieldAt_controlBlock, controlBlock]
  exact Complexity.Cobham.padTo_eq_append _ _ (by
    simpa [oneHotCode_length] using hwidth)

theorem fixedConfigurationCode_stackFieldAt (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) (k : tm.K) :
    fixedFieldAt (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) (stackFieldIndex tm k) =
      boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (cfg.stk k)) := by
  rw [fixedFieldAt_configurationField tm finiteAlphabets capacity cfg
    (Fin.succ (Fintype.equivFin tm.K k))]
  simp only [fixedConfigurationFields, Equiv.symm_apply_apply]
  have hlen :
      (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (cfg.stk k))).length =
      (fixedFieldRuler tm finiteAlphabets capacity).length := by
    simp [fixedFieldRuler, fixedFieldWidth, boundedStackCode_length]
  rw [Complexity.Cobham.padTo_eq_append _ _ (by omega)]
  simp [hlen]
theorem fixedConfigurationCode_stackTopDecomp (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (hcapacity : 0 < capacity) (cfg : tm.Cfg) (k : tm.K) :
    ∃ cell payload,
      fixedFieldAt (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity cfg) (stackFieldIndex tm k) =
          stackCellCode tm finiteAlphabets cell ++ payload ∧
      decodeStackCellAt tm k cell = (cfg.stk k).head? := by
  cases capacity with
  | zero => omega
  | succ capacity =>
      cases hstack : cfg.stk k with
      | nil =>
          refine ⟨none, boundedStackCode tm finiteAlphabets capacity [], ?_, ?_⟩
          · rw [fixedConfigurationCode_stackFieldAt]
            simp [hstack, taggedStack, boundedStackCode_succ_nil]
          · rfl
      | cons symbol rest =>
          refine ⟨some (k, symbol),
            boundedStackCode tm finiteAlphabets capacity (taggedStack tm k rest), ?_, ?_⟩
          · rw [fixedConfigurationCode_stackFieldAt]
            simp [hstack, taggedStack, boundedStackCode_succ_cons]
          · simp [decodeStackCellAt]

/-- The structural compiler agrees with the actual upstream `stepAux` on every
canonical configuration whose internal push slack fits the fixed stack fields.
The per-constructor induction discharges all nested `Stmt` transitions. -/
theorem stmtFieldMap_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (stmt : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (cfg : tm.Cfg)
    (hcapacity : 0 < capacity)
    (hcontrolWidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      (fixedFieldRuler tm finiteAlphabets capacity).length)
    (hslack : forall k, (cfg.stk k).length + Runtime.statementPushBound stmt <= capacity) :
    stmtFieldMap tm finiteAlphabets stmt
      ![fixedFieldRuler tm finiteAlphabets capacity,
        fixedConfigurationCode tm finiteAlphabets capacity cfg] =
      fixedConfigurationCode tm finiteAlphabets capacity
        (Turing.TM2.stepAux stmt cfg.var cfg.stk) := by
  induction stmt generalizing cfg capacity hcapacity hcontrolWidth hslack with
  | push k f next ih =>
      let cfg' : tm.Cfg :=
        { cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k) }
      have hslack' := statementPushSlack_after_push tm next k f cfg.var cfg.stk
        capacity hslack
      have hcontrol := fixedConfigurationCode_controlSplit tm finiteAlphabets capacity cfg
        hcontrolWidth
      have hstack := fixedConfigurationCode_stackFieldAt tm finiteAlphabets capacity cfg k

      have hpush : pushFieldsMap tm finiteAlphabets k f
          (fixedFieldRuler tm finiteAlphabets capacity)
          (fixedConfigurationCode tm finiteAlphabets capacity cfg) =
          fixedConfigurationCode tm finiteAlphabets capacity cfg' := by
        unfold pushFieldsMap
        rw [pushCellFromControl_correct tm finiteAlphabets k f
          (fixedFieldRuler tm finiteAlphabets capacity)
          (fixedConfigurationCode tm finiteAlphabets capacity cfg) cfg.var cfg.l
          (List.replicate ((fixedFieldRuler tm finiteAlphabets capacity).length -
            (oneHotCode (cfg.l, cfg.var)).length) false) hcontrol]
        rw [stackFieldDynamicPushMap_correct tm
          (fixedFieldRuler tm finiteAlphabets capacity)
          (fixedConfigurationCode tm finiteAlphabets capacity cfg)
          (stackCellCode tm finiteAlphabets (some (k, f cfg.var)))
          (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (cfg.stk k)))
          k hstack]
        rw [boundedStackCode_push_dynamic tm finiteAlphabets capacity hcapacity
          (k, f cfg.var) (taggedStack tm k (cfg.stk k))]
        exact (fixedConfigurationCode_stackUpdate tm finiteAlphabets capacity cfg k
          (f cfg.var :: cfg.stk k)).symm
      change stmtFieldMap tm finiteAlphabets next
          ![fixedFieldRuler tm finiteAlphabets capacity,
            pushFieldsMap tm finiteAlphabets k f
              (fixedFieldRuler tm finiteAlphabets capacity)
              (fixedConfigurationCode tm finiteAlphabets capacity cfg)] = _
      rw [hpush]
      simpa [cfg', Turing.TM2.stepAux] using
        (ih cfg' capacity hcapacity hcontrolWidth hslack')
  | peek k f next ih =>
      let cfg' : tm.Cfg := { cfg with var := f cfg.var (cfg.stk k).head? }
      have hslack' := statementPushSlack_after_peek tm next k f cfg.stk capacity hslack
      have hcontrol := fixedConfigurationCode_controlSplit tm finiteAlphabets capacity cfg
        hcontrolWidth
      obtain ⟨cell, payload, hcell, hdecode⟩ :=
        fixedConfigurationCode_stackTopDecomp tm finiteAlphabets capacity hcapacity cfg k
      have hmap := peekControlFieldMap_correct tm finiteAlphabets k f
        (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity cfg)
        (cfg.l, cfg.var) cell
        (List.replicate ((fixedFieldRuler tm finiteAlphabets capacity).length -
          (oneHotCode (cfg.l, cfg.var)).length) false) payload hcontrol hcell
      have hcanonical := fixedConfigurationCode_controlUpdate tm finiteAlphabets capacity cfg
        cfg.l (f cfg.var (cfg.stk k).head?)
      change stmtFieldMap tm finiteAlphabets next
          ![fixedFieldRuler tm finiteAlphabets capacity,
            peekControlFieldMap tm finiteAlphabets k f
              (fixedFieldRuler tm finiteAlphabets capacity)
              (fixedConfigurationCode tm finiteAlphabets capacity cfg)] = _
      rw [hmap, hdecode, ← hcanonical]
      simpa [cfg', Turing.TM2.stepAux] using
        (ih cfg' capacity hcapacity hcontrolWidth hslack')
  | pop k f next ih =>
      have hslack' := statementPushSlack_after_pop tm next k f cfg.var cfg.stk
        capacity hslack
      have hcontrol := fixedConfigurationCode_controlSplit tm finiteAlphabets capacity cfg
        hcontrolWidth
      obtain ⟨cell, payload, hcell, hdecode⟩ :=
        fixedConfigurationCode_stackTopDecomp tm finiteAlphabets capacity hcapacity cfg k
      cases hstack : cfg.stk k with
      | nil =>
          let cfgStack : tm.Cfg := { cfg with stk := Function.update cfg.stk k [] }
          let cfg' : tm.Cfg := { cfgStack with var := f cfg.var none }
          have hmap := popFieldsMap_actual_empty tm finiteAlphabets capacity hcapacity k f
            (fixedFieldRuler tm finiteAlphabets capacity)
            (fixedConfigurationCode tm finiteAlphabets capacity cfg) (cfg.l, cfg.var)
            (List.replicate ((fixedFieldRuler tm finiteAlphabets capacity).length -
              (oneHotCode (cfg.l, cfg.var)).length) false) hcontrol
            (by rw [fixedConfigurationCode_stackFieldAt, hstack]; simp [taggedStack])
          have hstackCode := fixedConfigurationCode_stackUpdate tm finiteAlphabets capacity
            cfg k []
          have hcontrolCode := fixedConfigurationCode_controlUpdate tm finiteAlphabets
            capacity cfgStack cfg.l (f cfg.var none)
          have hmap' : popFieldsMap tm finiteAlphabets k f
              (fixedFieldRuler tm finiteAlphabets capacity)
              (fixedConfigurationCode tm finiteAlphabets capacity cfg) =
              fixedConfigurationCode tm finiteAlphabets capacity cfg' := by
            rw [hmap, ← hstackCode, ← hcontrolCode]
            simp [cfg', cfgStack, hstack]
          change stmtFieldMap tm finiteAlphabets next
              ![fixedFieldRuler tm finiteAlphabets capacity,
                popFieldsMap tm finiteAlphabets k f
                  (fixedFieldRuler tm finiteAlphabets capacity)
                  (fixedConfigurationCode tm finiteAlphabets capacity cfg)] = _
          rw [hmap']
          simpa [cfg', Turing.TM2.stepAux] using
            (ih cfg' capacity hcapacity hcontrolWidth hslack')
      | cons symbol rest =>
          let cfgStack : tm.Cfg := { cfg with stk := Function.update cfg.stk k rest }
          let cfg' : tm.Cfg := { cfgStack with var := f cfg.var (some symbol) }
          have htailfit : rest.length < capacity := by
            have hk := hslack k
            simp [Runtime.statementPushBound] at hk
            simp [hstack] at hk
            simp
            omega
          have hmap := popFieldsMap_actual_nonempty tm finiteAlphabets capacity hcapacity k f
            (fixedFieldRuler tm finiteAlphabets capacity)
            (fixedConfigurationCode tm finiteAlphabets capacity cfg) (cfg.l, cfg.var)
            (List.replicate ((fixedFieldRuler tm finiteAlphabets capacity).length -
              (oneHotCode (cfg.l, cfg.var)).length) false) symbol rest htailfit hcontrol
            (by rw [fixedConfigurationCode_stackFieldAt, hstack]; simp [taggedStack])
          have hstackCode := fixedConfigurationCode_stackUpdate tm finiteAlphabets capacity
            cfg k rest
          have hcontrolCode := fixedConfigurationCode_controlUpdate tm finiteAlphabets
            cfgStack cfg.l (f cfg.var (some symbol))
          have hmap' : popFieldsMap tm finiteAlphabets k f
              (fixedFieldRuler tm finiteAlphabets capacity)
              (fixedConfigurationCode tm finiteAlphabets capacity cfg) =
              fixedConfigurationCode tm finiteAlphabets capacity cfg' := by
            rw [hmap, ← hstackCode, ← hcontrolCode]
            simp [cfg', cfgStack, hstack]
          change stmtFieldMap tm finiteAlphabets next
              ![fixedFieldRuler tm finiteAlphabets capacity,
                popFieldsMap tm finiteAlphabets k f
                  (fixedFieldRuler tm finiteAlphabets capacity)
                  (fixedConfigurationCode tm finiteAlphabets capacity cfg)] = _
          rw [hmap']
          simpa [cfg', Turing.TM2.stepAux] using
            (ih cfg' capacity hcapacity hcontrolWidth hslack')
  | load f next ih =>
      let cfg' : tm.Cfg := { cfg with var := f cfg.var }
      have hslack' := statementPushSlack_after_load tm next f cfg.stk capacity hslack
      have hmap := controlFieldMap_canonical tm finiteAlphabets capacity cfg
        (fun pair => (pair.1, f pair.2)) hcontrolWidth
      change stmtFieldMap tm finiteAlphabets next
          ![fixedFieldRuler tm finiteAlphabets capacity,
            controlFieldMap tm (fixedFieldRuler tm finiteAlphabets capacity)
              (fixedConfigurationCode tm finiteAlphabets capacity cfg)
              (fun pair => (pair.1, f pair.2))] = _
      rw [hmap]
      simpa [cfg', Turing.TM2.stepAux] using
        (ih cfg' capacity hcapacity hcontrolWidth hslack')
  | branch condition yes no ihYes ihNo =>
      have hslackBranches := statementPushSlack_after_branch tm condition yes no
        cfg.stk capacity hslack
      have hcontrol := fixedConfigurationCode_controlSplit tm finiteAlphabets capacity cfg
        hcontrolWidth
      have hbranch := branchFieldMap_correct tm condition
        (stmtFieldMap tm finiteAlphabets yes) (stmtFieldMap tm finiteAlphabets no)
        (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity cfg) (cfg.l, cfg.var)
        (List.replicate ((fixedFieldRuler tm finiteAlphabets capacity).length -
          (oneHotCode (cfg.l, cfg.var)).length) false) hcontrol
      change branchFieldMap tm condition (stmtFieldMap tm finiteAlphabets yes)
          (stmtFieldMap tm finiteAlphabets no)
          (fixedFieldRuler tm finiteAlphabets capacity)
          (fixedConfigurationCode tm finiteAlphabets capacity cfg) = _
      rw [hbranch]
      by_cases hcondition : condition cfg.var
      · rw [if_pos hcondition]
        simpa [Turing.TM2.stepAux, hcondition] using
          (ihYes cfg capacity hcapacity hcontrolWidth hslackBranches.1)
      · rw [if_neg hcondition]
        simpa [Turing.TM2.stepAux, hcondition] using
          (ihNo cfg capacity hcapacity hcontrolWidth hslackBranches.2)
  | goto target =>
      have hmap := controlFieldMap_canonical tm finiteAlphabets capacity cfg
        (fun pair => (some (target pair.2), pair.2)) hcontrolWidth
      change controlFieldMap tm (fixedFieldRuler tm finiteAlphabets capacity)
          (fixedConfigurationCode tm finiteAlphabets capacity cfg)
          (fun pair => (some (target pair.2), pair.2)) = _
      rw [hmap]
      simp [Turing.TM2.stepAux]
  | halt =>
      have hmap := controlFieldMap_canonical tm finiteAlphabets capacity cfg
        (fun pair => (none, pair.2)) hcontrolWidth
      change controlFieldMap tm (fixedFieldRuler tm finiteAlphabets capacity)
          (fixedConfigurationCode tm finiteAlphabets capacity cfg)
          (fun pair => (none, pair.2)) = _
      rw [hmap]
      simp [Turing.TM2.stepAux]
/-- On a canonical configuration with enough per-stack push budget, the
finite dispatch over the actual program label agrees with the actual upstream
`stepAux` result. The resource premise is derived from the imported program
push bound; it is not a caller-supplied encoded-step assumption. -/
theorem programStatementDispatch_stepAux_correct (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg)
    (hcapacity : 0 < capacity)
    (hcontrolWidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      (fixedFieldRuler tm finiteAlphabets capacity).length)
    (hslack : forall k, (cfg.stk k).length + Runtime.programPushBound tm <= capacity) :
    programStatementDispatch tm finiteAlphabets
      (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) =
      fixedConfigurationCode tm finiteAlphabets capacity
        (match cfg.l with
         | none => cfg
         | some label => Turing.TM2.stepAux (tm.m label) cfg.var cfg.stk) := by
  have hdispatch := programStatementDispatch_correct tm finiteAlphabets capacity cfg
    hcontrolWidth
  cases hlabel : cfg.l with
  | none => simpa [hlabel] using hdispatch
  | some label =>
      rw [hdispatch]
      have hstmtSlack : forall k,
          (cfg.stk k).length + Runtime.statementPushBound (tm.m label) <= capacity := by
        intro k
        have hprogram := Runtime.statement_le_programPushBound tm label
        have hk := hslack k
        omega
      have hstmt := stmtFieldMap_correct tm finiteAlphabets capacity (tm.m label) cfg
        hcapacity hcontrolWidth hstmtSlack
      simpa [hlabel] using hstmt

/-- The ruler for an entire serialized configuration repeats one field ruler
for the control slot and every physical stack slot. -/
def wholeConfigurationRuler (tm : Turing.FinTM2) (fieldRuler : List Bool) : List Bool :=
  (List.replicate (Fintype.card tm.K + 1) fieldRuler).flatten

/-- Totalized program step: every arbitrary input, including malformed or
over-capacity codes, is normalized to the fixed whole-configuration width. -/
def normalizedProgramStep (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (fieldRuler state : List Bool) : List Bool :=
  Complexity.Cobham.padTo (wholeConfigurationRuler tm fieldRuler)
    (programStatementDispatch tm finiteAlphabets fieldRuler state)

theorem wholeConfigurationRuler_mem (tm : Turing.FinTM2) :
    Complexity.Cobham (fun v : Fin 1 -> List Bool =>
      wholeConfigurationRuler tm (v 0)) := by
  exact (Complexity.Cobham.comp
    (Complexity.Cobham.repeatFn (Complexity.Cobham.proj 0)
      (Fintype.card tm.K + 1))
    (gs := ![Complexity.Cobham.proj 0])).of_eq (fun _ => rfl)

theorem normalizedProgramStep_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      normalizedProgramStep tm finiteAlphabets (v 0) (v 1)) := by
  have hruler : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      wholeConfigurationRuler tm (v 0)) :=
    (Complexity.Cobham.comp (wholeConfigurationRuler_mem tm)
      (gs := ![Complexity.Cobham.proj 0])).of_eq (fun _ => rfl)
  have hstep : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      programStatementDispatch tm finiteAlphabets (v 0) (v 1)) :=
    programStatementDispatch_mem tm finiteAlphabets
  exact (Complexity.Cobham.comp (Complexity.Cobham.padFn
      (Complexity.Cobham.proj 0) (Complexity.Cobham.proj 1))
      (gs := ![hruler, hstep])).of_eq (fun _ => rfl)

@[simp] theorem normalizedProgramStep_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (fieldRuler state : List Bool) :
    (normalizedProgramStep tm finiteAlphabets fieldRuler state).length =
      wholeConfigurationRuler tm fieldRuler |>.length := by
  simp [normalizedProgramStep, Complexity.Cobham.padTo_length]

/-- Normalize an arbitrary initial bitstring into the fixed whole-configuration
slot used by the iterator. On canonical initial codes this is identity. -/
def normalizeConfigurationState (tm : Turing.FinTM2)
    (fieldRuler state : List Bool) : List Bool :=
  Complexity.Cobham.padTo (wholeConfigurationRuler tm fieldRuler) state

theorem normalizeConfigurationState_mem (tm : Turing.FinTM2) :
    Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      normalizeConfigurationState tm (v 0) (v 1)) := by
  have hruler : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      wholeConfigurationRuler tm (v 0)) :=
    (Complexity.Cobham.comp (wholeConfigurationRuler_mem tm)
      (gs := ![Complexity.Cobham.proj 0])).of_eq (fun _ => rfl)
  exact (Complexity.Cobham.comp (Complexity.Cobham.padFn
      (Complexity.Cobham.proj 0) (Complexity.Cobham.proj 1))
      (gs := ![hruler, Complexity.Cobham.proj 1])).of_eq (fun _ => rfl)

/-- The iterator step uses the clock bitstring only as the iterFn clock and
reads its two fixed parameters as the field ruler and serialized configuration.
The step itself ignores the current clock symbol. -/
def clockedNormalizedProgramStep (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (v : Fin 3 -> List Bool) : List Bool :=
  normalizedProgramStep tm finiteAlphabets (v 1) (v 0)

theorem clockedNormalizedProgramStep_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Complexity.Cobham (clockedNormalizedProgramStep tm finiteAlphabets) := by
  exact (Complexity.Cobham.comp (normalizedProgramStep_mem tm finiteAlphabets)
    (gs := ![Complexity.Cobham.proj 1, Complexity.Cobham.proj 0])).of_eq
      (fun _ => rfl)

/-- Fixed-width initialization, total normalized transitions, and the same
fixed ruler give the all-clock bound required by the actual pinned `iterFn`.
The clock `c` is universally quantified; no runtime-sized clock is assumed. -/
theorem normalizedProgramIterFn_mem (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      ((fun s => clockedNormalizedProgramStep tm finiteAlphabets
          (Fin.cons s (Fin.tail v)))^[(v 0).length]
        (normalizeConfigurationState tm (v 1) (v 2)))) := by
  have he : Complexity.Cobham (fun v : Fin 2 -> List Bool =>
      normalizeConfigurationState tm (v 0) (v 1)) :=
    normalizeConfigurationState_mem tm
  have hf : Complexity.Cobham (clockedNormalizedProgramStep tm finiteAlphabets) :=
    clockedNormalizedProgramStep_mem tm finiteAlphabets
  have hj : Complexity.Cobham (fun v : Fin 3 -> List Bool =>
      wholeConfigurationRuler tm (v 1)) := by
    exact (Complexity.Cobham.comp (wholeConfigurationRuler_mem tm)
      (gs := ![Complexity.Cobham.proj 1])).of_eq (fun _ => rfl)
  have hbound : forall c v,
      ((fun s => clockedNormalizedProgramStep tm finiteAlphabets
          (Fin.cons s v))^[c.length]
        (normalizeConfigurationState tm (v 0) (v 1))).length <=
      (wholeConfigurationRuler tm (v 0)).length := by
    intro c v
    let step : List Bool -> List Bool := fun state =>
      normalizedProgramStep tm finiteAlphabets (v 0) state
    have hiter : (step^[c.length]
        (normalizeConfigurationState tm (v 0) (v 1))).length =
        (wholeConfigurationRuler tm (v 0)).length := by
      induction c.length with
      | zero => simp [normalizeConfigurationState, Complexity.Cobham.padTo_length]
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          simp [step, normalizedProgramStep_length]
    simpa [hiter, step, clockedNormalizedProgramStep]
  exact Complexity.Cobham.iterFn he hf hj hbound

/-- Unfolding the actual upstream option-valued step identifies its `getD`
totalization with the program-label case used by the finite dispatch. -/
theorem absorbingStep_eq_programCase (tm : Turing.FinTM2) (cfg : tm.Cfg) :
    absorbingStep tm cfg =
      match cfg.l with
      | none => cfg
      | some label => Turing.TM2.stepAux (tm.m label) cfg.var cfg.stk := by
  cases hlabel : cfg.l <;>
    simp [absorbingStep, Turing.FinTM2.step, Turing.TM2.step, hlabel]

theorem fixedConfigurationCode_length_eq_wholeRuler (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) :
    (fixedConfigurationCode tm finiteAlphabets capacity cfg).length =
      (wholeConfigurationRuler tm (fixedFieldRuler tm finiteAlphabets capacity)).length := by
  rw [fixedConfigurationCode_length]
  simp [wholeConfigurationRuler, fixedFieldRuler, fixedFieldWidth]

/-- On canonical reachable configurations with enough capacity, the total
normalized Cobham step is exactly the code of the actual absorbing TM2 step.
The only semantic premise is the concrete all-stack constructor push slack. -/
theorem normalizedProgramStep_actual (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg)
    (hcapacity : 0 < capacity)
    (hcontrolWidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      (fixedFieldRuler tm finiteAlphabets capacity).length)
    (hslack : forall k, (cfg.stk k).length + Runtime.programPushBound tm <= capacity) :
    normalizedProgramStep tm finiteAlphabets
        (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity cfg) =
      fixedConfigurationCode tm finiteAlphabets capacity (absorbingStep tm cfg) := by
  unfold normalizedProgramStep
  rw [programStatementDispatch_stepAux_correct tm finiteAlphabets capacity cfg
    hcapacity hcontrolWidth hslack]
  rw [absorbingStep_eq_programCase]
  have hlen := fixedConfigurationCode_length_eq_wholeRuler tm finiteAlphabets capacity
    (match cfg.l with
     | none => cfg
     | some label => Turing.TM2.stepAux (tm.m label) cfg.var cfg.stk)
  have hpad := Complexity.Cobham.padTo_eq_append
    (wholeConfigurationRuler tm (fixedFieldRuler tm finiteAlphabets capacity))
    (fixedConfigurationCode tm finiteAlphabets capacity
      (match cfg.l with
       | none => cfg
       | some label => Turing.TM2.stepAux (tm.m label) cfg.var cfg.stk))
    (by omega)
  rw [hpad, hlen]
  simp

/-- Every stack in the actual run has one program-step of internal push slack
strictly before the chosen external clock horizon. The estimate uses the
all-stack runtime bound and the extra capacity cell. -/
theorem absorbingRun_stepSlack (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (clockLength clock : Nat)
    (hclock : clock < clockLength) :
    forall k,
      (((absorbingStep tm)^[clock] (Turing.initList tm input)).stk k).length +
          Runtime.programPushBound tm <=
        fixedStackCapacity tm input.length clockLength := by
  intro k
  let bound : Nat := ∑ _k : tm.K, Runtime.programPushBound tm
  have hcard : 1 <= Fintype.card tm.K := by
    exact Fintype.card_pos_iff.mpr ⟨tm.k₀⟩
  have hsum : bound = Fintype.card tm.K * Runtime.programPushBound tm := by
    simp [bound]
  have hpush : Runtime.programPushBound tm <= bound := by
    rw [hsum]
    calc
      Runtime.programPushBound tm = 1 * Runtime.programPushBound tm := by simp
      _ <= Fintype.card tm.K * Runtime.programPushBound tm :=
        Nat.mul_le_mul_right _ hcard
  have hclock' : clock + 1 <= clockLength := Nat.succ_le_iff.mpr hclock
  have hbudget : clock * bound + Runtime.programPushBound tm <= clockLength * bound := by
    calc
      clock * bound + Runtime.programPushBound tm <= clock * bound + bound :=
        Nat.add_le_add_left hpush _
      _ = (clock + 1) * bound := by omega
      _ <= clockLength * bound := Nat.mul_le_mul_right _ hclock'
  have htotal := iterate_absorbingStep_stackLength_le tm clock (Turing.initList tm input)
  have hstack := stackLength_le_totalStackLength tm
    ((absorbingStep tm)^[clock] (Turing.initList tm input)) k
  have hinitial := initial_totalStackLength_le tm input
  have hsum' : (∑ _k : tm.K, Runtime.programPushBound tm) = bound := by rfl
  unfold fixedStackCapacity
  rw [← hsum'] at hbudget
  omega

/-- Up to any chosen clock horizon, the normalized Cobham transition iterates
exactly encode the actual upstream absorbing TM2 run. This proves that the
fixed-capacity truncation arm is unreachable at each real step. -/
theorem normalizedIterator_eq_actualRun (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (input : List (tm.Γ tm.k₀)) (clockLength clock : Nat)
    (hclock : clock <= clockLength) :
    (normalizedProgramStep tm finiteAlphabets
        (fixedFieldRuler tm finiteAlphabets
          (fixedStackCapacity tm input.length clockLength)) ^[clock]
      (normalizeConfigurationState tm
        (fixedFieldRuler tm finiteAlphabets
          (fixedStackCapacity tm input.length clockLength))
        (fixedConfigurationCode tm finiteAlphabets
          (fixedStackCapacity tm input.length clockLength) (Turing.initList tm input)))) =
    fixedConfigurationCode tm finiteAlphabets
      (fixedStackCapacity tm input.length clockLength)
      (((absorbingStep tm)^[clock]) (Turing.initList tm input)) := by
  let capacity := fixedStackCapacity tm input.length clockLength
  let ruler := fixedFieldRuler tm finiteAlphabets capacity
  have hcodeLength := fixedConfigurationCode_length_eq_wholeRuler tm
    finiteAlphabets capacity (Turing.initList tm input)
  have hinit : normalizeConfigurationState tm ruler
      (fixedConfigurationCode tm finiteAlphabets capacity (Turing.initList tm input)) =
      fixedConfigurationCode tm finiteAlphabets capacity (Turing.initList tm input) := by
    unfold normalizeConfigurationState
    have hpad := Complexity.Cobham.padTo_eq_append (wholeConfigurationRuler tm ruler)
      (fixedConfigurationCode tm finiteAlphabets capacity (Turing.initList tm input))
      (by rw [hcodeLength])
    rw [hpad, hcodeLength]
    simp
  have hcontrolWidth : Fintype.card (Prod (Option tm.Λ) tm.σ) <= ruler.length := by
    simpa [ruler, capacity, fixedStackCapacity, fixedFieldRuler, fixedFieldWidth] using
      (fixedFieldWidth_ge_controlCode tm finiteAlphabets input.length clockLength)
  have hcapacity : 0 < capacity := by
    simp [capacity, fixedStackCapacity]
  induction clock with
  | zero => simpa [hinit]
  | succ t ih =>
      have ht : t < clockLength := by omega
      have ih' := ih (by omega)
      have hslack := absorbingRun_stepSlack tm input clockLength t ht
      have hstep := normalizedProgramStep_actual tm finiteAlphabets capacity
        (((absorbingStep tm)^[t]) (Turing.initList tm input))
        hcapacity hcontrolWidth hslack
      calc
        (normalizedProgramStep tm finiteAlphabets ruler)^[t + 1]
            (normalizeConfigurationState tm ruler
              (fixedConfigurationCode tm finiteAlphabets capacity
                (Turing.initList tm input))) =
          normalizedProgramStep tm finiteAlphabets ruler
            (((normalizedProgramStep tm finiteAlphabets ruler)^[t])
              (normalizeConfigurationState tm ruler
                (fixedConfigurationCode tm finiteAlphabets capacity
                  (Turing.initList tm input)))) := by
              rw [Function.iterate_succ_apply']
        _ = normalizedProgramStep tm finiteAlphabets ruler
            (fixedConfigurationCode tm finiteAlphabets capacity
              (((absorbingStep tm)^[t]) (Turing.initList tm input))) := by rw [ih']
        _ = fixedConfigurationCode tm finiteAlphabets capacity
            (absorbingStep tm (((absorbingStep tm)^[t]) (Turing.initList tm input))) :=
              hstep
        _ = fixedConfigurationCode tm finiteAlphabets capacity
            (((absorbingStep tm)^[t + 1]) (Turing.initList tm input)) := by
              simp [Function.iterate_succ_apply']

/-- Compose the source-authored fixed-width iterator simulation with the
actual successful TM2 execution certificate. At any horizon covering its
budget, the Cobham iterator is the fixed-field encoding of the upstream
`haltList`; no encoded final-state equality is assumed by the caller. -/
theorem normalizedIterator_eq_haltList_of_EvalsToInTime (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    {budget : Nat} (clockLength : Nat)
    (execution : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some (Turing.haltList tm output)) budget) (hbudget : budget <= clockLength) :
    (normalizedProgramStep tm finiteAlphabets
        (fixedFieldRuler tm finiteAlphabets
          (fixedStackCapacity tm input.length clockLength)) ^[clockLength]
      (normalizeConfigurationState tm
        (fixedFieldRuler tm finiteAlphabets
          (fixedStackCapacity tm input.length clockLength))
        (fixedConfigurationCode tm finiteAlphabets
          (fixedStackCapacity tm input.length clockLength) (Turing.initList tm input)))) =
    fixedConfigurationCode tm finiteAlphabets
      (fixedStackCapacity tm input.length clockLength) (Turing.haltList tm output) := by
  rw [normalizedIterator_eq_actualRun tm finiteAlphabets input clockLength clockLength
    (Turing.le_refl clockLength)]
  rw [absorbingTM2Run_eq_haltList_after tm input output execution hbudget]


end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer
