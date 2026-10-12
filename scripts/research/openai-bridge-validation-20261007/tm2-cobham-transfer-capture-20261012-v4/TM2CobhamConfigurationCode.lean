import OAI.Computability.UniqueGames.Model
import OAI.Computability.UniqueGames.Machines.Runtime
import Complexitylib.Classes.P.Cobham.Internal.Algebra
import Complexitylib.Classes.P.Cobham.Vec

/-!
# Finite-alphabet whole-configuration code for the upstream TM2 model

Every physical stack symbol is represented by a fixed-width one-hot block in
one finite tagged alphabet. A configuration is then a fixed-arity vector: one
block for the finite control (label and register) and one string per stack. The
pinned `Cobham.encodeVec` turns that complete vector into a single bitstring.
-/

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer

open Turing

/-- A one-hot code of constant width for a value in a fixed finite carrier. -/
noncomputable def oneHotCode {α : Type} [Fintype α] (a : α) : List Bool :=
  List.ofFn fun i : Fin (Fintype.card α) => decide (i = Fintype.equivFin α a)

@[simp] theorem oneHotCode_length {α : Type} [Fintype α] (a : α) :
    (oneHotCode a).length = Fintype.card α := by
  simp [oneHotCode]

theorem oneHotCode_injective {α : Type} [Fintype α] :
    Function.Injective (oneHotCode : α → List Bool) := by
  intro a b h
  have hfun := List.ofFn_injective h
  apply (Fintype.equivFin α).injective
  have hbit := congrFun hfun (Fintype.equivFin α a)
  have hindex : decide (Fintype.equivFin α a = Fintype.equivFin α b) = true := by
    simpa using hbit
  exact of_decide_eq_true hindex

/-- The disjoint tagged alphabet of all actual TM2 stack alphabets. -/
abbrev TaggedStackSymbol (tm : Turing.FinTM2) := Σ k : tm.K, tm.Γ k

/-- The all-stack finiteness premise is converted into the single finite table
used by the common-width block encoder. -/
noncomputable def taggedAlphabetFintype (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Fintype (TaggedStackSymbol tm) := by
  classical
  letI : forall k : tm.K, Finite (tm.Γ k) := finiteAlphabets
  letI : forall k : tm.K, Fintype (tm.Γ k) := fun k => Fintype.ofFinite (tm.Γ k)
  exact inferInstance

/-- The fixed bit width used for every tagged stack symbol. -/
noncomputable def taggedAlphabetWidth (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm) :
    Nat := by
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  exact Fintype.card (TaggedStackSymbol tm)

/-- A physical stack symbol receives its one-hot block in the tagged alphabet. -/
noncomputable def taggedSymbolCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (symbol : TaggedStackSymbol tm) : List Bool := by
  letI : Fintype (TaggedStackSymbol tm) := taggedAlphabetFintype tm finiteAlphabets
  exact oneHotCode symbol

@[simp] theorem taggedSymbolCode_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (symbol : TaggedStackSymbol tm) :
    (taggedSymbolCode tm finiteAlphabets symbol).length =
      taggedAlphabetWidth tm finiteAlphabets := by
  simp [taggedSymbolCode, taggedAlphabetWidth, taggedAlphabetFintype]

/-- A stack is encoded top-first as the concatenation of its fixed-width
symbol blocks. Its physical stack index is carried by each tag. -/
noncomputable def stackBlock (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (stack : List (tm.Γ k)) : List Bool :=
  (stack.map fun symbol => taggedSymbolCode tm finiteAlphabets ⟨k, symbol⟩).flatten

theorem stackBlock_length (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (k : tm.K) (stack : List (tm.Γ k)) :
    (stackBlock tm finiteAlphabets k stack).length =
      stack.length * taggedAlphabetWidth tm finiteAlphabets := by
  induction stack with
  | nil => simp [stackBlock]
  | cons symbol rest ih =>
      simp [stackBlock, ih, taggedSymbolCode_length]
      omega

/-- Finite control has a single fixed-width code containing both the optional
label and the register value. -/
noncomputable def controlBlock (tm : Turing.FinTM2) (cfg : tm.Cfg) : List Bool :=
  oneHotCode (cfg.l, cfg.var)

/-- A whole TM2 configuration is encoded as one control field followed by one
independently framed stack field for every finite stack index. -/
noncomputable def configurationFields (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cfg : tm.Cfg) : Fin (Fintype.card tm.K + 1) → List Bool :=
  Fin.cons (controlBlock tm cfg) fun i =>
    let k := (Fintype.equivFin tm.K).symm i
    stackBlock tm finiteAlphabets k (cfg.stk k)

/-- The complete configuration bitstring used by the Cobham iteration. -/
noncomputable def configurationCode (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cfg : tm.Cfg) : List Bool :=
  Complexity.Cobham.encodeVec (configurationFields tm finiteAlphabets cfg)

/-- The vector width used by `encodeVec` is exactly the control block plus the
sum of the fixed-width stack blocks. -/
theorem configurationFields_vectorLength (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cfg : tm.Cfg) :
    Complexity.Cobham.vectorLength (configurationFields tm finiteAlphabets cfg) =
      (controlBlock tm cfg).length +
        taggedAlphabetWidth tm finiteAlphabets * totalStackLength tm cfg := by
  rw [Complexity.Cobham.vectorLength_succ]
  simp only [configurationFields, Fin.cons_zero, Fin.tail_cons]
  rw [Complexity.Cobham.vectorLength]
  rw [Equiv.sum_comp (Fintype.equivFin tm.K)
    (fun k : tm.K => (stackBlock tm finiteAlphabets k (cfg.stk k)).length)]
  simp [stackBlock_length, totalStackLength, Finset.sum_mul, Nat.mul_comm]

/-- The complete bitstring configuration has an explicit linear-in-stack-size
length bound; its constants depend only on the fixed finite machine alphabets,
control and arity. -/
theorem configurationCode_length_le (tm : Turing.FinTM2)
    (finiteAlphabets :
      OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet tm)
    (cfg : tm.Cfg) :
    (configurationCode tm finiteAlphabets cfg).length ≤
      2 ^ (Fintype.card tm.K + 1) *
        ((controlBlock tm cfg).length +
          taggedAlphabetWidth tm finiteAlphabets * totalStackLength tm cfg +
          2 * (Fintype.card tm.K + 1)) := by
  rw [configurationCode]
  calc
    (Complexity.Cobham.encodeVec (configurationFields tm finiteAlphabets cfg)).length ≤
        2 ^ (Fintype.card tm.K + 1) *
          (Complexity.Cobham.vectorLength
              (configurationFields tm finiteAlphabets cfg) +
            2 * (Fintype.card tm.K + 1)) :=
      Complexity.Cobham.encodeVec_length_le _
    _ = _ := by rw [configurationFields_vectorLength]

/-- A total transition that leaves every halted configuration fixed. `TM2.step`
returns `some` on the clock that executes a `.halt` constructor, with label `none`;
all subsequent clocks return `none`, and this definition keeps that final state. -/
def absorbingStep (tm : Turing.FinTM2) (cfg : tm.Cfg) : tm.Cfg :=
  (tm.step cfg).getD cfg

theorem absorbingStep_stackLength_le (tm : Turing.FinTM2) (cfg : tm.Cfg) :
    totalStackLength tm (absorbingStep tm cfg) ≤
      totalStackLength tm cfg + ∑ _k : tm.K, Runtime.programPushBound tm := by
  unfold absorbingStep
  cases h : tm.step cfg with
  | none => simp [h, totalStackLength]
  | some next =>
      exact step_totalStackLength_le tm cfg next h

theorem iterate_absorbingStep_stackLength_le (tm : Turing.FinTM2)
    (clock : Nat) (cfg : tm.Cfg) :
    totalStackLength tm ((absorbingStep tm)^[clock] cfg) ≤
      totalStackLength tm cfg + clock * (∑ _k : tm.K, Runtime.programPushBound tm) := by
  induction clock with
  | zero => simp
  | succ clock ih =>
      have hstep := absorbingStep_stackLength_le tm ((absorbingStep tm)^[clock] cfg)
      rw [Nat.add_mul, Nat.one_mul]
      simpa only [Function.iterate_succ_apply'] using Nat.le_trans hstep
        (Nat.add_le_add_right ih _)

end OAI.UniqueGamesTheorem.Foundations.Complexity.TM2CobhamTransfer
