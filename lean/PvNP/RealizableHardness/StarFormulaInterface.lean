import PvNP.RealizableHardness.Formula
import PvNP.RealizableHardness.StarListDecoding
import Mathlib.Data.Finset.Dedup

namespace PvNP.RealizableHardness.StarFormulaInterface
open PvNP.RealizableHardness.StarListDecoding
open scoped BigOperators
noncomputable section
universe u v
variable {V : Type u} [Fintype V]
  {Sigma : V → Type v} [∀ x, Fintype (Sigma x)]
  [∀ x, Nonempty (Sigma x)] {m : ℕ}

def evalOpt {X : Type*} (Z : X → Bool) : Option (Formula X) → Bool
  | none => false
  | some f => f.eval Z

def orOpt {X : Type*} : Option (Formula X) → Option (Formula X) → Option (Formula X)
  | none, q => q | some p, none => some p | some p, some q => some (.or p q)

def andOpt {X : Type*} : Option (Formula X) → Option (Formula X) → Option (Formula X)
  | some p, some q => some (.and p q) | _, _ => none

def orMany {X : Type*} (fs : List (Option (Formula X))) : Option (Formula X) := fs.foldr orOpt none
def andMany {X : Type*} (fs : List (Option (Formula X))) (acc : Option (Formula X)) : Option (Formula X) := fs.foldl andOpt acc

def selected (Z : (Σ x, Sigma x) → Bool) (x : V) : Finset (Sigma x) := by
  classical exact Finset.univ.filter (fun a => Z ⟨x, a⟩ = true)

def leafVertices (e : Star V Sigma m) : Finset V := by
  classical exact Finset.univ.image e.leaf

def fibre (e : Star V Sigma m) (x : V) (b : Sigma e.center) : Finset (Sigma x) := by
  classical exact Finset.univ.filter (fun a => ∀ i : Fin m, ∀ h : e.leaf i = x,
    e.projection i (cast (congrArg Sigma h.symm) a) = b)

def LocalWitness (e : Star V Sigma m) (A : ∀ x, Finset (Sigma x)) : Prop :=
  ∃ b : Sigma e.center, b ∈ A e.center ∧ ∀ x ∈ leafVertices e, ∃ a : Sigma x, a ∈ A x ∧ a ∈ fibre e x b

def leafFormula (e : Star V Sigma m) (x : V) (b : Sigma e.center) : Option (Formula (Σ x, Sigma x)) :=
  orMany ((fibre e x b).toList.map (fun a => some (.var ⟨x, a⟩)))

def branch (e : Star V Sigma m) (b : Sigma e.center) : Option (Formula (Σ x, Sigma x)) :=
  andMany ((leafVertices e).toList.map (fun x => leafFormula e x b)) (some (.var ⟨e.center, b⟩))

def compile (e : Star V Sigma m) : Option (Formula (Σ x, Sigma x)) :=
  orMany ((Finset.univ : Finset (Sigma e.center)).toList.map (branch e))

theorem evalOpt_orOpt {X : Type*} (Z : X → Bool) (p q : Option (Formula X)) :
    evalOpt Z (orOpt p q) = (evalOpt Z p || evalOpt Z q) := by cases p <;> cases q <;> simp [orOpt, evalOpt, Formula.eval]
theorem evalOpt_andOpt {X : Type*} (Z : X → Bool) (p q : Option (Formula X)) :
    evalOpt Z (andOpt p q) = (evalOpt Z p && evalOpt Z q) := by cases p <;> cases q <;> simp [andOpt, evalOpt, Formula.eval]

theorem eval_orMany_iff {X : Type*} (Z : X → Bool) (fs : List (Option (Formula X))) :
    evalOpt Z (orMany fs) = true ↔ ∃ f ∈ fs, evalOpt Z f = true := by
  induction fs with
  | nil => simp [orMany, evalOpt]
  | cons a fs ih =>
      change evalOpt Z (orOpt a (orMany fs)) = true ↔ _
      rw [evalOpt_orOpt, Bool.or_eq_true_iff, ih]
      simp [Bool.or_eq_true]

theorem eval_andMany_iff {X : Type*} (Z : X → Bool) (fs : List (Option (Formula X))) (acc : Option (Formula X)) :
    evalOpt Z (andMany fs acc) = true ↔ evalOpt Z acc = true ∧ ∀ f ∈ fs, evalOpt Z f = true := by
  induction fs generalizing acc with
  | nil => simp [andMany]
  | cons a fs ih =>
      change evalOpt Z (andMany fs (andOpt acc a)) = true ↔ _
      rw [ih, evalOpt_andOpt]
      simp [Bool.and_eq_true, and_assoc]

theorem localWitness_iff_listWitness (e : Star V Sigma m) (A : ∀ x, Finset (Sigma x)) :
    LocalWitness e A ↔ e.listWitness A := by
  classical
  constructor
  · rintro ⟨b, hb, hx⟩
    let q : Labeling Sigma := fun x => if h : x = e.center then cast (congrArg Sigma h.symm) b else
      if h : x ∈ leafVertices e then Classical.choose (hx x h) else Classical.choice (inferInstance : Nonempty (Sigma x))
    have hleafmem (i : Fin m) : e.leaf i ∈ leafVertices e :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hqcenter : q e.center = b := by simp [q]
    have hqleaf (i : Fin m) : q (e.leaf i) = Classical.choose (hx (e.leaf i) (hleafmem i)) := by
      simp [q, hleafmem, (e.separated i).symm]
    refine ⟨q, ?_, ?_⟩
    · intro i
      have hi := (Classical.choose_spec (hx (e.leaf i) (hleafmem i))).2
      have hmem := Finset.mem_filter.mp hi
      rw [hqleaf i, hqcenter]
      exact hmem.2 i rfl
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · change q e.center ∈ A e.center
        rw [hqcenter]
        exact hb
      · change q (e.leaf i) ∈ A (e.leaf i)
        rw [hqleaf i]
        exact (Classical.choose_spec (hx (e.leaf i) (hleafmem i))).1
  · rintro ⟨l, hl, hA⟩
    refine ⟨l e.center, hA 0, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp hx
    refine ⟨l x, ?_, ?_⟩
    · have hmem : l (e.leaf i) ∈ A (e.leaf i) := hA i.succ
      exact hxi ▸ hmem
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · intro j h
      have hcast : cast (congrArg Sigma h.symm) (l x) = l (e.leaf j) := by
        cases h
        rfl
      rw [hcast]
      exact hl j

theorem eval_all_true {X : Type*} (f : Formula X) : f.eval (fun _ => true) = true := by
  induction f <;> simp [Formula.eval, *]

theorem eval_leafFormula_iff (e : Star V Sigma m) (Z : (Σ x, Sigma x) → Bool)
    (x : V) (b : Sigma e.center) :
    evalOpt Z (leafFormula e x b) = true ↔
      ∃ a ∈ fibre e x b, Z ⟨x, a⟩ = true := by
  classical
  rw [leafFormula, eval_orMany_iff]
  simp [List.mem_map, Formula.eval, evalOpt]

theorem eval_branch_iff (e : Star V Sigma m) (Z : (Σ x, Sigma x) → Bool)
    (b : Sigma e.center) :
    evalOpt Z (branch e b) = true ↔
      Z ⟨e.center, b⟩ = true ∧
      ∀ x ∈ leafVertices e, ∃ a ∈ fibre e x b, Z ⟨x, a⟩ = true := by
  classical
  rw [branch, eval_andMany_iff]
  change Z ⟨e.center, b⟩ = true ∧ _ ↔ _
  simp [eval_leafFormula_iff]

theorem eval_compile_iff_listWitness (e : Star V Sigma m)
    (Z : (Σ x, Sigma x) → Bool) :
    evalOpt Z (compile e) = true ↔ e.listWitness (selected Z) := by
  classical
  have hlocal : evalOpt Z (compile e) = true ↔ LocalWitness e (selected Z) := by
    simp [compile, eval_orMany_iff, eval_branch_iff, LocalWitness, selected,
      Star.slot, and_assoc, and_left_comm, and_comm]
  exact hlocal.trans (localWitness_iff_listWitness e (selected Z))

theorem compile_eq_none_iff (e : Star V Sigma m) :
    compile e = none ↔ ¬ ∃ l : Labeling Sigma, e.accepts l := by
  classical
  constructor
  · intro hc
    intro hex
    obtain ⟨l, hl⟩ := hex
    have hw : e.listWitness (selected (fun _ => true)) := by
      refine ⟨l, hl, ?_⟩
      intro j
      simp [selected]
    have he := (eval_compile_iff_listWitness e (fun _ => true)).mpr hw
    rw [hc] at he
    simp [evalOpt] at he
  · intro hn
    cases hc : compile e with
    | none => rfl
    | some f =>
      exfalso
      apply hn
      have hf : f.eval (fun _ => true) = true := eval_all_true f
      have he : evalOpt (fun _ => true) (compile e) = true := by
        rw [hc]
        exact hf
      have hw := (eval_compile_iff_listWitness e (fun _ => true)).mp he
      obtain ⟨l, hl, hmem⟩ := hw
      exact ⟨l, hl⟩

theorem compile_some_eval_iff (e : Star V Sigma m)
    (f : Formula (Σ x, Sigma x)) (hf : compile e = some f)
    (Z : (Σ x, Sigma x) → Bool) :
    f.eval Z = true ↔ e.listWitness (selected Z) := by
  rw [← eval_compile_iff_listWitness e Z, hf]
  rfl

end
end PvNP.RealizableHardness.StarFormulaInterface
