import PvNP.RealizableHardness.StarFormulaInterface

namespace PvNP.RealizableHardness.StarFormulaInterfaceChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.StarListDecoding
open PvNP.RealizableHardness.StarFormulaInterface
noncomputable section

def zero : Star Bool (fun _ => Bool) 0 where
  center := false
  leaf := Fin.elim0
  projection := fun i => Fin.elim0 i
  separated := fun i => Fin.elim0 i

def repeated : Star Bool (fun _ => Bool) 2 where
  center := false
  leaf := fun _ => true
  projection := fun _ a => a
  separated := fun _ => by decide

def conflicting : Star Bool (fun _ => Bool) 2 where
  center := false
  leaf := fun _ => true
  projection := fun i a => if i = 0 then a else !a
  separated := fun _ => by decide

def Mixed : Bool → Type
  | false => Bool
  | true => Unit

instance (x : Bool) : Fintype (Mixed x) := by
  cases x
  · change Fintype Bool
    infer_instance
  · change Fintype Unit
    infer_instance
instance (x : Bool) : Nonempty (Mixed x) := by
  cases x
  · change Nonempty Bool
    infer_instance
  · change Nonempty Unit
    infer_instance

def unitLeaf : Star Bool Mixed 1 where
  center := false
  leaf := fun _ => true
  projection := fun _ _ => false
  separated := fun _ => by decide

def chooseFalse : (Sigma fun _ : Bool => Bool) → Bool := fun z => !z.2
def mixedSelection : (Sigma Mixed) → Bool
  | ⟨false, b⟩ => !b
  | ⟨true, _⟩ => true

example :
    (∀ Z : (Sigma fun _ : Bool => Bool) → Bool,
      evalOpt Z (compile zero) = (Z ⟨false, false⟩ || Z ⟨false, true⟩)) ∧
    evalOpt (fun _ => false) (compile zero) = false ∧
    evalOpt chooseFalse (compile zero) = true := by
  classical
  letI : DecidableEq Bool := instDecidableEqBool
  have hall : ∀ Z : (Sigma fun _ : Bool => Bool) → Bool,
      evalOpt Z (compile zero) = (Z ⟨false, false⟩ || Z ⟨false, true⟩) := by
    intro Z
    have hiff : evalOpt Z (compile zero) = true ↔
        Z ⟨false, false⟩ = true ∨ Z ⟨false, true⟩ = true := by
      rw [eval_compile_iff_listWitness]
      constructor
      · intro hw
        obtain ⟨l, hl, hs⟩ := hw
        have hc : l false ∈ selected Z false := by
          simpa [zero, Star.slot] using hs 0
        have hz : Z ⟨false, l false⟩ = true := (Finset.mem_filter.mp hc).2
        cases hb : l false with
        | false => exact Or.inl (by simpa only [hb] using hz)
        | true => exact Or.inr (by simpa only [hb] using hz)
      · intro h
        apply (localWitness_iff_listWitness zero (selected Z)).mp
        rcases h with h | h
        · refine ⟨false, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, ?_⟩
          intro x hx
          have hempty : leafVertices zero = ∅ := by simp [leafVertices, zero]
          rw [hempty] at hx
          simp at hx
        · refine ⟨true, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, ?_⟩
          intro x hx
          have hempty : leafVertices zero = ∅ := by simp [leafVertices, zero]
          rw [hempty] at hx
          simp at hx
    cases h : evalOpt Z (compile zero) <;> cases h0 : Z ⟨false, false⟩ <;>
      cases h1 : Z ⟨false, true⟩ <;> simp_all
  exact ⟨hall, by simpa using hall (fun _ => false), by simpa [chooseFalse] using hall chooseFalse⟩

example : evalOpt chooseFalse (compile repeated) = true := by
  classical
  rw [eval_compile_iff_listWitness]
  let l : Labeling (fun _ : Bool => Bool) := fun _ => false
  refine ⟨l, ?_, ?_⟩
  · intro i; rfl
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change l false ∈ selected chooseFalse false
      simp [l, selected, chooseFalse]
    · change l true ∈ selected chooseFalse true
      simp [l, selected, chooseFalse]

example : compile conflicting = none := by
  classical
  apply (compile_eq_none_iff conflicting).mpr
  rintro ⟨l, hl⟩
  have h0 := hl (0 : Fin 2)
  have h1 := hl (1 : Fin 2)
  simp [conflicting] at h0 h1
  cases l true <;> simp_all

example :
    fibre unitLeaf true true = ∅ ∧
    fibre unitLeaf true false = Finset.univ ∧
    (∃ f, compile unitLeaf = some f) ∧
    evalOpt mixedSelection (compile unitLeaf) = true := by
  classical
  constructor
  · ext a
    simp [fibre, unitLeaf]
  constructor
  · ext a
    simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_univ]
    constructor
    · intro _; trivial
    · intro _ i h; rfl
  constructor
  · let l : Labeling Mixed := fun x => match x with | false => false | true => ()
    have hw : unitLeaf.listWitness (selected mixedSelection) := by
      refine ⟨l, ?_, ?_⟩
      · intro i; rfl
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · change l false ∈ selected mixedSelection false
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, rfl⟩
        · change l true ∈ selected mixedSelection true
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, rfl⟩
    have he := (eval_compile_iff_listWitness unitLeaf mixedSelection).mpr hw
    cases hc : compile unitLeaf with
    | none => simp [hc, evalOpt] at he
    | some f => exact ⟨f, rfl⟩
  · let l : Labeling Mixed := fun x => match x with | false => false | true => ()
    have hw : unitLeaf.listWitness (selected mixedSelection) := by
      refine ⟨l, ?_, ?_⟩
      · intro i; rfl
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · change l false ∈ selected mixedSelection false
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, rfl⟩
        · change l true ∈ selected mixedSelection true
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, rfl⟩
    exact (eval_compile_iff_listWitness unitLeaf mixedSelection).mpr hw

example : ∃ f, compile repeated = some f ∧ f.eval (fun _ => false) = false := by
  classical
  let l : Labeling (fun _ : Bool => Bool) := fun _ => false
  have haccept : repeated.accepts l := by
    intro i; simp [repeated, l]
  have hsome : ∃ f, compile repeated = some f := by
    cases hc : compile repeated with
    | none =>
      exfalso
      apply (compile_eq_none_iff repeated).mp hc
      exact ⟨l, haccept⟩
    | some f => exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hsome
  refine ⟨f, hf, ?_⟩
  have hw : ¬ repeated.listWitness (selected (fun _ => false)) := by
    intro h
    obtain ⟨l, hl, hs⟩ := h
    have hc := hs 0
    simp [selected, repeated] at hc
  have hv := (compile_some_eval_iff repeated f hf (fun _ => false))
  cases he : f.eval (fun _ => false) with
  | false => rfl
  | true => exact False.elim (hw (hv.mp he))

#print axioms PvNP.RealizableHardness.StarFormulaInterface.evalOpt_orOpt
#print axioms PvNP.RealizableHardness.StarFormulaInterface.evalOpt_andOpt
#print axioms PvNP.RealizableHardness.StarFormulaInterface.eval_orMany_iff
#print axioms PvNP.RealizableHardness.StarFormulaInterface.eval_andMany_iff
#print axioms PvNP.RealizableHardness.StarFormulaInterface.localWitness_iff_listWitness
#print axioms PvNP.RealizableHardness.StarFormulaInterface.eval_all_true
#print axioms PvNP.RealizableHardness.StarFormulaInterface.eval_leafFormula_iff
#print axioms PvNP.RealizableHardness.StarFormulaInterface.eval_branch_iff
#print axioms PvNP.RealizableHardness.StarFormulaInterface.eval_compile_iff_listWitness
#print axioms PvNP.RealizableHardness.StarFormulaInterface.compile_eq_none_iff
#print axioms PvNP.RealizableHardness.StarFormulaInterface.compile_some_eval_iff

#check PvNP.RealizableHardness.StarFormulaInterface.localWitness_iff_listWitness
#check PvNP.RealizableHardness.StarFormulaInterface.eval_compile_iff_listWitness
#check PvNP.RealizableHardness.StarFormulaInterface.compile_eq_none_iff
#check PvNP.RealizableHardness.StarFormulaInterface.compile_some_eval_iff

end
end PvNP.RealizableHardness.StarFormulaInterfaceChecks
