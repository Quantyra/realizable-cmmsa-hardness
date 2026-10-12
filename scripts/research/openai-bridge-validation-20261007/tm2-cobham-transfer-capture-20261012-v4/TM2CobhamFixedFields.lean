import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Complexitylib.Classes.P.Cobham.Vec
import TM2CobhamBoundedStack

/-!
# Addressable padded fields for the TM2 state code

All fields use one ruler. `blockFn` reads a field and `replaceFixedField`
updates one field; both are derived from the pinned Cobham algebra operations.
The semantic configuration constructor is included to state the fixed-size
invariant for every upstream configuration.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

open Complexity.Cobham

def fixedFieldWidth (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) : Nat :=
  capacity * stackCellWidth tm finiteAlphabets

def fixedFieldRuler (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) : List Bool :=
  List.replicate (fixedFieldWidth tm finiteAlphabets capacity) false

/-- Control then one field per physical stack, each padded or truncated to the
same ruler width. -/
noncomputable def fixedConfigurationFields (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) : Fin (Fintype.card tm.K + 1) → List Bool :=
  Fin.cons
    (Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
      (controlBlock tm cfg))
    (fun i =>
      let k := (Fintype.equivFin tm.K).symm i
      Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
        (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k (cfg.stk k))))

noncomputable def fixedConfigurationCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) : List Bool :=
  (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity cfg)).flatten

theorem fixedConfigurationCode_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) :
    (fixedConfigurationCode tm finiteAlphabets capacity cfg).length =
      (Fintype.card tm.K + 1) * fixedFieldWidth tm finiteAlphabets capacity := by
  simp [fixedConfigurationCode, fixedConfigurationFields, fixedFieldRuler,
    fixedFieldWidth, Complexity.Cobham.padTo_length]

/-- Read field `i` using the pinned block-addressing operation. -/
def fixedFieldAt (ruler state : List Bool) (i : Nat) : List Bool :=
  Complexity.Cobham.blockAt ruler state i

theorem fixedFieldAt_mem (i : Nat) :
    Cobham fun v : Fin 2 → List Bool => fixedFieldAt (v 0) (v 1) i := by
  exact Cobham.blockFn (Cobham.proj 0) (Cobham.proj 1) i

/-- Replace field `i`, padding or truncating the new value to the shared ruler.
The result is total on arbitrary bitstrings and has the same length as the
input whenever the input already consists of whole fields. -/
def replaceFixedField (ruler state value : List Bool) (i : Nat) : List Bool :=
  state.take (i * ruler.length) ++ Complexity.Cobham.padTo ruler value ++
    state.drop ((i + 1) * ruler.length)

theorem replaceFixedField_mem (i : Nat) :
    Cobham fun v : Fin 3 → List Bool =>
      replaceFixedField (v 0) (v 1) (v 2) i := by
  have hprefix : Cobham fun v : Fin 3 → List Bool =>
      (v 1).take ((List.replicate i (v 0)).flatten.length) :=
    Cobham.takeFn (Cobham.repeatFn (Cobham.proj 0) i) (Cobham.proj 1)
  have hmiddle : Cobham fun v : Fin 3 → List Bool =>
      Complexity.Cobham.padTo (v 0) (v 2) :=
    Cobham.padFn (Cobham.proj 0) (Cobham.proj 2)
  have hsuffix : Cobham fun v : Fin 3 → List Bool =>
      (v 1).drop ((List.replicate (i + 1) (v 0)).flatten.length) :=
    Cobham.dropFn (Cobham.repeatFn (Cobham.proj 0) (i + 1)) (Cobham.proj 1)
  exact (Cobham.appendFn (Cobham.appendFn hprefix hmiddle) hsuffix).of_eq fun _ => by
    simp [replaceFixedField, List.length_flatten]

/-- The capacity reserve includes enough bits for the full finite control
code even on the empty input and clock-zero boundary cases. -/
theorem fixedFieldWidth_ge_controlCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (inputLength clockLength : Nat) :
    Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      fixedFieldWidth tm finiteAlphabets (fixedStackCapacity tm inputLength clockLength) := by
  have hcell := stackCellWidth_pos tm finiteAlphabets
  have hcap : Fintype.card (Prod (Option tm.Λ) tm.σ) <=
      fixedStackCapacity tm inputLength clockLength := by
    unfold fixedStackCapacity
    omega
  calc
    Fintype.card (Prod (Option tm.Λ) tm.σ) <=
        fixedStackCapacity tm inputLength clockLength := hcap
    _ <= fixedStackCapacity tm inputLength clockLength *
        stackCellWidth tm finiteAlphabets :=
      Nat.le_mul_of_pos_right _ hcell
    _ = fixedFieldWidth tm finiteAlphabets
        (fixedStackCapacity tm inputLength clockLength) := rfl
/-- Block zero of the serialized configuration is exactly the padded
finite control code. -/
theorem fixedFieldAt_controlBlock (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) :
    fixedFieldAt (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) 0 =
      Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
        (controlBlock tm cfg) := by
  simp [fixedFieldAt, fixedConfigurationCode, fixedConfigurationFields,
    fixedFieldRuler, blockAt]

/-- Every serialized field is recoverable from the complete fixed-width
configuration code. This is the bridge used to state constructor correctness
against the actual `Cfg` representation. -/
theorem fixedFieldAt_configurationField (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg)
    (i : Fin (Fintype.card tm.K + 1)) :
    fixedFieldAt (fixedFieldRuler tm finiteAlphabets capacity)
      (fixedConfigurationCode tm finiteAlphabets capacity cfg) i.val =
      fixedConfigurationFields tm finiteAlphabets capacity cfg i := by
  unfold fixedFieldAt fixedConfigurationCode
  rw [Complexity.Cobham.blockAt_flatten]
  · simp
  · intro b hb
    simp [fixedConfigurationFields, fixedFieldRuler, Complexity.Cobham.padTo_length]

/-- Replacing field `i` in a concatenation of equal-width fields agrees with
flattening the field list after replacing that component. -/
theorem replaceFixedField_flatten (r : List Bool)
    (fields : List (List Bool))
    (hwidth : forall b, b ∈ fields -> b.length = r.length)
    (i : Nat) (hi : i < fields.length) (value : List Bool) :
    replaceFixedField r fields.flatten value i =
      (fields.take i ++ Complexity.Cobham.padTo r value :: fields.drop (i + 1)).flatten := by
  induction fields generalizing i with
  | nil => simp at hi
  | cons field fields ih =>
      cases i with
      | zero =>
          have hfield := hwidth field (by simp)
          simp [replaceFixedField, List.flatten_cons, hfield,
            Complexity.Cobham.padTo_length]
      | succ i =>
          have hfield := hwidth field (by simp)
          have htail : forall b, b ∈ fields -> b.length = r.length := by
            intro b hb
            exact hwidth b (by simp [hb])
          have hbound : i < fields.length := by omega
          have hrec := ih htail i hbound value
          simp [replaceFixedField, List.flatten_cons, Nat.succ_mul,
            List.take_append, List.drop_append, hfield,
            Complexity.Cobham.padTo_length, hrec]

/-- Every control/stack field in a canonical configuration has the common
ruler width. -/
theorem fixedConfigurationFields_width (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) :
    forall i, (fixedConfigurationFields tm finiteAlphabets capacity cfg i).length =
      (fixedFieldRuler tm finiteAlphabets capacity).length := by
  intro i
  simp [fixedConfigurationFields, fixedFieldRuler, Complexity.Cobham.padTo_length]

/-- If a constructor's canonical field list is obtained by replacing one
padded field, its complete configuration code is exactly the pinned flat
field replacement on the previous code. -/
theorem fixedConfigurationCode_replaceField (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (before after : tm.Cfg)
    (i : Fin (Fintype.card tm.K + 1)) (value : List Bool)
    (hfields : List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity after) =
      (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity before)).take i.val ++
        Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity) value ::
        (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity before)).drop (i.val + 1)) :
    fixedConfigurationCode tm finiteAlphabets capacity after =
      replaceFixedField (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity before) value i.val := by
  have hwidth : forall b,
      b ∈ List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity before) ->
      b.length = (fixedFieldRuler tm finiteAlphabets capacity).length := by
    intro b hb
    rcases List.mem_ofFn.mp hb with ⟨j, rfl⟩
    exact fixedConfigurationFields_width tm finiteAlphabets capacity before j
  have hi : i.val < (List.ofFn
      (fixedConfigurationFields tm finiteAlphabets capacity before)).length := by simp
  unfold fixedConfigurationCode
  rw [hfields]
  symm
  exact replaceFixedField_flatten (fixedFieldRuler tm finiteAlphabets capacity)
    (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity before)) hwidth
    i.val hi value

/-- A control-only Cfg update changes exactly field zero in the canonical
field list; every physical stack field is preserved verbatim. -/
theorem fixedConfigurationFields_controlUpdate (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) (label : Option tm.Λ) (state : tm.σ) :
    List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity
      { cfg with l := label, var := state }) =
      [Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
        (oneHotCode (label, state))] ++
        (List.ofFn (fixedConfigurationFields tm finiteAlphabets capacity cfg)).drop 1 := by
  simp [fixedConfigurationFields, fixedFieldRuler, controlBlock,
    Complexity.Cobham.padTo_length]

theorem fixedConfigurationCode_controlUpdate (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) (label : Option tm.Λ) (state : tm.σ) :
    fixedConfigurationCode tm finiteAlphabets capacity
      { cfg with l := label, var := state } =
      replaceFixedField (fixedFieldRuler tm finiteAlphabets capacity)
        (fixedConfigurationCode tm finiteAlphabets capacity cfg)
        (oneHotCode (label, state)) 0 := by
  apply fixedConfigurationCode_replaceField tm finiteAlphabets capacity cfg
    { cfg with l := label, var := state } ⟨0, Nat.zero_lt_succ _⟩
    (oneHotCode (label, state))
  simpa using fixedConfigurationFields_controlUpdate tm finiteAlphabets
    capacity cfg label state

/-- Finite function updates are represented by the corresponding list update
under `List.ofFn`. -/
theorem list_ofFn_update {alpha : Type} {n : Nat}
    (fields : Fin n -> alpha) (i : Fin n) (value : alpha) :
    List.ofFn (Function.update fields i value) = (List.ofFn fields).set i.val value := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero => simp [List.ofFn_succ]
      | succ i => simp [List.ofFn_succ, ih]

/-- Updating one actual physical stack updates exactly the corresponding
successor field in the canonical control-plus-stacks vector. -/
theorem fixedConfigurationFields_stackUpdate (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (capacity : Nat) (cfg : tm.Cfg) (k : tm.K) (stack : List (tm.Γ k)) :
    fixedConfigurationFields tm finiteAlphabets capacity
        { cfg with stk := Function.update cfg.stk k stack } =
      Function.update (fixedConfigurationFields tm finiteAlphabets capacity cfg)
        (Fin.succ (Fintype.equivFin tm.K k))
        (Complexity.Cobham.padTo (fixedFieldRuler tm finiteAlphabets capacity)
          (boundedStackCode tm finiteAlphabets capacity (taggedStack tm k stack))) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [fixedConfigurationFields]
  | succ i =>
      by_cases h : i = Fintype.equivFin tm.K k
      · subst i
        simp [fixedConfigurationFields, Function.update]
      · simp [fixedConfigurationFields, Function.update, h,
          Equiv.symm_apply_eq]
end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer
