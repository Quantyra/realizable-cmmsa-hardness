import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The concrete four-equation equality gadget for the source occurrence reduction.
Variables 0,1 are terminals x,y; variables 2,3,4,5,6 are a,b,c,d,e.
This constant gadget is not a source-hardness or running-time theorem.
-/
namespace PvNP.RealizableHardness.EqualityGadget

abbrev Var := Fin 7
abbrev Row := Fin 4
abbrev Assignment := Var → ZMod 2

/-- Ordered triples retain equation occurrence identity for later serialization. -/
def row : Row → Fin 3 → Var :=
  ![![0, 2, 3], ![1, 4, 5], ![2, 4, 6], ![3, 5, 6]]

def rhs (_ : Row) : ZMod 2 := 0

def rows : List ((Fin 3 → Var) × ZMod 2) :=
  List.ofFn (fun r : Row => (row r, rhs r))

def satisfied (s : Assignment) (r : Row) : Prop :=
  s (row r 0) + s (row r 1) + s (row r 2) = rhs r

instance (s : Assignment) (r : Row) : Decidable (satisfied s r) :=
  inferInstanceAs (Decidable (_ = _))

def violations (s : Assignment) : Nat :=
  (Finset.univ.filter (fun r : Row => ¬ satisfied s r)).card

def mismatch (x y : ZMod 2) : Nat := if x = y then 0 else 1

/-- The explicit attaining assignment: a=c=e=0, b=x, d=y. -/
def extension (x y : ZMod 2) : Assignment := ![x, y, 0, x, 0, y, 0]

def support (r : Row) : Finset Var := Finset.univ.image (row r)

def degree (v : Var) : Nat :=
  (Finset.univ.filter (fun r : Row => v ∈ support r)).card

theorem rows_length : rows.length = 4 := by decide

theorem rows_nodup : rows.Nodup := by decide

theorem row_injective : ∀ r : Row, Function.Injective (row r) := by decide

theorem support_card : ∀ r : Row, (support r).card = 3 := by decide

theorem support_injective : Function.Injective support := by decide

theorem pair_intersection :
    ∀ r t : Row, r ≠ t → (support r ∩ support t).card ≤ 1 := by decide

theorem degree_exact : ∀ v : Var, degree v = if v < 2 then 1 else 2 := by decide

theorem extension_terminals (x y : ZMod 2) :
    extension x y 0 = x ∧ extension x y 1 = y := by
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 10000 in
theorem violations_lower :
    ∀ s : Assignment, mismatch (s 0) (s 1) ≤ violations s := by decide

theorem extension_violations :
    ∀ x y : ZMod 2, violations (extension x y) = mismatch x y := by decide

/-- The minimum is realized, with every assignment with those terminals bounded below. -/
theorem exact_minimum (x y : ZMod 2) :
    (∀ s : Assignment, s 0 = x → s 1 = y → mismatch x y ≤ violations s) ∧
    (∃ s : Assignment, s 0 = x ∧ s 1 = y ∧ violations s = mismatch x y) := by
  constructor
  · intro s hx hy
    simpa only [hx, hy] using violations_lower s
  · exact ⟨extension x y, rfl, rfl, extension_violations x y⟩

set_option maxRecDepth 10000 in
theorem all_satisfied_implies_equal :
    ∀ s : Assignment, (∀ r : Row, satisfied s r) → s 0 = s 1 := by decide

theorem satisfiable_iff_equal (x y : ZMod 2) :
    (∃ s : Assignment, s 0 = x ∧ s 1 = y ∧ ∀ r : Row, satisfied s r) ↔ x = y := by
  constructor
  · rintro ⟨s, hx, hy, hs⟩
    simpa only [hx, hy] using all_satisfied_implies_equal s hs
  · intro h
    subst y
    refine ⟨extension x x, rfl, rfl, ?_⟩
    have h : ∀ z : ZMod 2, ∀ r : Row, satisfied (extension z z) r := by decide
    exact h x

section Relabel
variable {V : Type*} [DecidableEq V] (f : Var ↪ V)

def relabeledRow (r : Row) (i : Fin 3) : V := f (row r i)

def relabeledRows : List ((Fin 3 → V) × ZMod 2) :=
  List.ofFn (fun r : Row => (relabeledRow f r, rhs r))

def relabeledSupport (r : Row) : Finset V := (support r).map f

theorem relabeledSupport_eq (r : Row) :
    relabeledSupport f r = Finset.univ.image (relabeledRow f r) := by
  ext v
  simp [relabeledSupport, support, relabeledRow, Finset.mem_map, Finset.mem_image]

theorem relabeled_row_injective (r : Row) :
    Function.Injective (relabeledRow f r) := f.injective.comp (row_injective r)

theorem relabeled_support_card (r : Row) : (relabeledSupport f r).card = 3 := by
  simpa only [relabeledSupport, Finset.card_map] using support_card r

theorem relabeled_support_injective : Function.Injective (relabeledSupport f) :=
  (Finset.map_injective f).comp support_injective

theorem relabeled_pair_intersection (r t : Row) (h : r ≠ t) :
    (relabeledSupport f r ∩ relabeledSupport f t).card ≤ 1 := by
  simpa only [relabeledSupport, ← Finset.map_inter, Finset.card_map]
    using pair_intersection r t h

def relabeledDegree (v : V) : Nat :=
  (Finset.univ.filter (fun r : Row => v ∈ relabeledSupport f r)).card

theorem relabeled_degree (v : Var) :
    relabeledDegree f (f v) = if v < 2 then 1 else 2 := by
  simpa [relabeledDegree, relabeledSupport, degree] using degree_exact v

theorem relabeled_degree_outside (v : V) (h : v ∉ Set.range f) :
    relabeledDegree f v = 0 := by
  have hn (r : Row) : v ∉ relabeledSupport f r := by
    intro hv
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hv
    exact h ⟨u, hu⟩
  simp [relabeledDegree, hn]

def relabeledSatisfied (s : V → ZMod 2) (r : Row) : Prop :=
  s (relabeledRow f r 0) + s (relabeledRow f r 1) + s (relabeledRow f r 2) = rhs r

theorem relabeled_satisfied (s : V → ZMod 2) (r : Row) :
    relabeledSatisfied f s r ↔ satisfied (s ∘ f) r := Iff.rfl

/-- Lower bound on the actual relabeled rows, for every global assignment. -/
theorem relabeled_violations_lower (s : V → ZMod 2) :
    mismatch (s (f 0)) (s (f 1)) ≤
      (Finset.univ.filter (fun r : Row =>
        ¬ (s (relabeledRow f r 0) + s (relabeledRow f r 1) +
          s (relabeledRow f r 2) = rhs r))).card :=
  violations_lower (s ∘ f)

end Relabel
end PvNP.RealizableHardness.EqualityGadget
