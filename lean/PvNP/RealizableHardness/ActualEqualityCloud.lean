import PvNP.RealizableHardness.ActualGraphEdges
import PvNP.RealizableHardness.EqualityGadget
import Mathlib.Algebra.BigOperators.Fin

/-! Source-only allocation of actual equality-gadget copies on the fixed graph.
The sum type keeps shared graph ports separate from fresh orbit-indexed internals. -/
namespace PvNP.RealizableHardness.ActualEqualityCloud
open ActualGraphEdges
open scoped BigOperators
set_option autoImplicit false
noncomputable section

abbrev GlobalVar (n : Nat) := Vertex n ⊕ (Edge n × Fin 5)
abbrev RowId (n : Nat) := Edge n × EqualityGadget.Row

/-- x,y are shared ports; a,b,c,d,e are fresh for this edge occurrence. -/
def embedFn {n : Nat} (e : Edge n) : EqualityGadget.Var → GlobalVar n :=
  ![Sum.inl e.val.1, Sum.inl (reverse e.val).1,
    Sum.inr (e,0), Sum.inr (e,1), Sum.inr (e,2), Sum.inr (e,3), Sum.inr (e,4)]

theorem embedFn_injective {n : Nat} (e : Edge n) : Function.Injective (embedFn e) := by
  have h := edge_terminals_distinct e
  have hr := Ne.symm h
  intro u v he
  fin_cases u <;> fin_cases v <;> simp_all [embedFn]

def embedding {n : Nat} (e : Edge n) : EqualityGadget.Var ↪ GlobalVar n :=
  ⟨embedFn e, embedFn_injective e⟩

theorem internal_identity {n : Nat} (e f : Edge n) (i j : Fin 5) :
    (Sum.inr (e,i) : GlobalVar n) = Sum.inr (f,j) ↔ e = f ∧ i = j := by simp

theorem internal_not_port {n : Nat} (e : Edge n) (i : Fin 5) (p : Vertex n) :
    (Sum.inr (e,i) : GlobalVar n) ≠ Sum.inl p := by simp

def row {n : Nat} (q : RowId n) : Fin 3 → GlobalVar n :=
  EqualityGadget.relabeledRow (embedding q.1) q.2

def rhs {n : Nat} (q : RowId n) : ZMod 2 := EqualityGadget.rhs q.2

def support {n : Nat} (q : RowId n) : Finset (GlobalVar n) :=
  EqualityGadget.relabeledSupport (embedding q.1) q.2

def localRows {n : Nat} (e : Edge n) : List ((Fin 3 → GlobalVar n) × ZMod 2) :=
  EqualityGadget.relabeledRows (embedding e)

/-- Retains precisely the order of the actual graph representative list. -/
def edgeList (n : Nat) : List (Edge n) :=
  (representativeList n).attach.map (fun d => ⟨d.val, mem_representativeList.mp d.property⟩)

def rows (n : Nat) : List ((Fin 3 → GlobalVar n) × ZMod 2) :=
  (edgeList n).flatMap localRows

theorem mem_edgeList {n : Nat} (e : Edge n) : e ∈ edgeList n := by
  have h : e.val ∈ representativeList n := mem_representativeList.mpr e.property
  apply List.mem_map.mpr
  exact ⟨⟨e.val,h⟩, by simp, rfl⟩

theorem edgeList_nodup (n : Nat) : (edgeList n).Nodup := by
  unfold edgeList
  apply (representativeList_nodup n).attach.map
  intro a b h
  apply Subtype.ext
  exact congrArg (fun d : Edge n => d.val) h

theorem edgeList_toFinset (n : Nat) : (edgeList n).toFinset = Finset.univ := by
  ext e
  simp [mem_edgeList]

theorem edgeList_length (n : Nat) : (edgeList n).length = Fintype.card (Edge n) := by
  rw [← List.toFinset_card_of_nodup (edgeList_nodup n), edgeList_toFinset]
  exact Finset.card_univ

theorem localRows_eq {n : Nat} (e : Edge n) :
    localRows e = List.ofFn (fun r : EqualityGadget.Row => (row (e,r), rhs (e,r))) := rfl

theorem row_mem_rows {n : Nat} (e : Edge n) (r : EqualityGadget.Row) :
    (row (e,r), rhs (e,r)) ∈ rows n := by
  apply List.mem_flatMap.mpr
  refine ⟨e, mem_edgeList e, ?_⟩
  rw [localRows_eq]
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

theorem row_injective {n : Nat} (q : RowId n) : Function.Injective (row q) :=
  EqualityGadget.relabeled_row_injective (embedding q.1) q.2

theorem support_eq {n : Nat} (q : RowId n) : support q = Finset.univ.image (row q) :=
  EqualityGadget.relabeledSupport_eq (embedding q.1) q.2

theorem support_card {n : Nat} (q : RowId n) : (support q).card = 3 :=
  EqualityGadget.relabeled_support_card (embedding q.1) q.2

/-- Each concrete gadget row uses at most one of its terminal variables. -/
theorem local_terminal_unique : ∀ r : EqualityGadget.Row,
    ∀ u ∈ EqualityGadget.support r, ∀ v ∈ EqualityGadget.support r,
      u < 2 → v < 2 → u = v := by decide

/-- Sharing across different copies can only happen at the two terminal slots. -/
theorem shared_implies_terminals {n : Nat} (e f : Edge n) (h : e ≠ f)
    (u v : EqualityGadget.Var) (he : embedFn e u = embedFn f v) : u < 2 ∧ v < 2 := by
  fin_cases u <;> fin_cases v <;> simp_all [embedFn]

theorem shared_member_terminal {n : Nat} (e f : Edge n) (h : e ≠ f)
    (r s : EqualityGadget.Row) (x : GlobalVar n)
    (hx : x ∈ support (e,r)) (hy : x ∈ support (f,s)) :
    ∃ u ∈ EqualityGadget.support r, u < 2 ∧ embedFn e u = x := by
  change x ∈ (EqualityGadget.support r).map (embedding e) at hx
  change x ∈ (EqualityGadget.support s).map (embedding f) at hy
  obtain ⟨u, hu, hux⟩ := Finset.mem_map.mp hx
  obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hy
  have he : embedFn e u = embedFn f v := hux.trans hvx.symm
  exact ⟨u, hu, (shared_implies_terminals e f h u v he).1, hux⟩

theorem cross_copy_intersection {n : Nat} (e f : Edge n) (h : e ≠ f)
    (r s : EqualityGadget.Row) : (support (e,r) ∩ support (f,s)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨u, hu, hut, hux⟩ := shared_member_terminal e f h r s x
    (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
  obtain ⟨v, hv, hvt, hvy⟩ := shared_member_terminal e f h r s y
    (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2
  have he := local_terminal_unique r u hu v hv hut hvt
  exact hux.symm.trans ((congrArg (embedFn e) he).trans hvy)

/-- Distinct equation occurrences, including parallel-edge copies, intersect at most once. -/
theorem pair_intersection {n : Nat} (a b : RowId n) (h : a ≠ b) :
    (support a ∩ support b).card ≤ 1 := by
  rcases a with ⟨e,r⟩
  rcases b with ⟨f,s⟩
  by_cases he : e = f
  · subst f
    have hr : r ≠ s := fun hrs => h (Prod.ext rfl hrs)
    exact EqualityGadget.relabeled_pair_intersection (embedding e) r s hr
  · exact cross_copy_intersection e f he r s

theorem support_injective (n : Nat) : Function.Injective (@support n) := by
  intro a b he
  by_contra hn
  have h := pair_intersection a b hn
  rw [he, Finset.inter_self, support_card] at h
  omega

/-- One assignment simultaneously makes every edge's five fresh internal choices. -/
def extension {n : Nat} (x : Vertex n → ZMod 2) : GlobalVar n → ZMod 2
  | Sum.inl p => x p
  | Sum.inr (e,i) => (![0, x e.val.1, 0, x (reverse e.val).1, 0] : Fin 5 → ZMod 2) i

theorem extension_ports {n : Nat} (x : Vertex n → ZMod 2) (p : Vertex n) :
    extension x (Sum.inl p) = x p := rfl

theorem extension_pullback {n : Nat} (x : Vertex n → ZMod 2) (e : Edge n) :
    extension x ∘ embedding e = EqualityGadget.extension (x e.val.1) (x (reverse e.val).1) := by
  funext u
  fin_cases u <;> rfl

def localViolations {n : Nat} (x : GlobalVar n → ZMod 2) (e : Edge n) : Nat :=
  EqualityGadget.violations (x ∘ embedding e)

theorem localViolations_eq {n : Nat} (x : GlobalVar n → ZMod 2) (e : Edge n) :
    localViolations x e = (Finset.univ.filter (fun r : EqualityGadget.Row =>
      ¬ (x (row (e,r) 0) + x (row (e,r) 1) + x (row (e,r) 2) = rhs (e,r)))).card := rfl

theorem local_lower {n : Nat} (x : GlobalVar n → ZMod 2) (e : Edge n) :
    EqualityGadget.mismatch (x (Sum.inl e.val.1)) (x (Sum.inl (reverse e.val).1)) ≤
      localViolations x e := EqualityGadget.violations_lower (x ∘ embedding e)

theorem extension_attains {n : Nat} (x : Vertex n → ZMod 2) (e : Edge n) :
    localViolations (extension x) e =
      EqualityGadget.mismatch (x e.val.1) (x (reverse e.val).1) := by
  rw [localViolations, extension_pullback]
  exact EqualityGadget.extension_violations _ _

def totalViolations {n : Nat} (x : GlobalVar n → ZMod 2) : Nat :=
  ∑ e : Edge n, localViolations x e

/-- Simultaneous attainment holds for arbitrary port assignments, not only constant ones. -/
theorem extension_total {n : Nat} (x : Vertex n → ZMod 2) :
    totalViolations (extension x) =
      ∑ e : Edge n, EqualityGadget.mismatch (x e.val.1) (x (reverse e.val).1) := by
  unfold totalViolations
  exact Finset.sum_congr rfl (fun e _ => extension_attains x e)

def badRow {n : Nat} (x : GlobalVar n → ZMod 2)
    (q : (Fin 3 → GlobalVar n) × ZMod 2) : Bool :=
  decide (¬ (x (q.1 0) + x (q.1 1) + x (q.1 2) = q.2))

def rowsViolations {n : Nat} (x : GlobalVar n → ZMod 2) : Nat :=
  (rows n).countP (badRow x)

private theorem countP_as_sum {A : Type*} (p : A → Bool) (l : List A) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]

theorem localRows_violations {n : Nat} (x : GlobalVar n → ZMod 2) (e : Edge n) :
    (localRows e).countP (badRow x) = localViolations x e := by
  rw [countP_as_sum, localRows_eq, List.map_ofFn, Fin.sum_ofFn,
    localViolations_eq, Finset.card_filter]
  simp only [Function.comp_def, badRow, decide_eq_true_eq]

/-- The indexed sum counts the exact generated ordered row list, with its occurrences. -/
theorem rowsViolations_eq_total {n : Nat} (x : GlobalVar n → ZMod 2) :
    rowsViolations x = totalViolations x := by
  unfold rowsViolations rows
  rw [List.countP_flatMap]
  simp_rw [Function.comp_def, localRows_violations]
  rw [← List.sum_toFinset (localViolations x) (edgeList_nodup n), edgeList_toFinset]
  rfl

theorem total_eq_filter_length {n : Nat} (x : GlobalVar n → ZMod 2) :
    totalViolations x = ((rows n).filter (badRow x)).length := by
  rw [← rowsViolations_eq_total]
  exact List.countP_eq_length_filter

/-- Exact simultaneous optimum on the generated list, rather than a separate semantic sum. -/
theorem extension_rows {n : Nat} (x : Vertex n → ZMod 2) :
    ((rows n).filter (badRow (extension x))).length =
      ∑ e : Edge n, EqualityGadget.mismatch (x e.val.1) (x (reverse e.val).1) := by
  rw [← total_eq_filter_length, extension_total]

theorem rows_lower {n : Nat} (x : GlobalVar n → ZMod 2) :
    (∑ e : Edge n, EqualityGadget.mismatch
      (x (Sum.inl e.val.1)) (x (Sum.inl (reverse e.val).1))) ≤
      ((rows n).filter (badRow x)).length := by
  rw [← total_eq_filter_length]
  exact Finset.sum_le_sum (fun e _ => local_lower x e)

/-- Every competing global assignment with the same port values has at least this cost. -/
theorem exact_minimum {n : Nat} (x : Vertex n → ZMod 2) :
    (∀ y : GlobalVar n → ZMod 2, (∀ p, y (Sum.inl p) = x p) →
      (∑ e : Edge n, EqualityGadget.mismatch (x e.val.1) (x (reverse e.val).1)) ≤
        ((rows n).filter (badRow y)).length) ∧
    (∃ y : GlobalVar n → ZMod 2, (∀ p, y (Sum.inl p) = x p) ∧
      ((rows n).filter (badRow y)).length =
        ∑ e : Edge n, EqualityGadget.mismatch (x e.val.1) (x (reverse e.val).1)) := by
  constructor
  · intro y hy
    simpa only [hy] using rows_lower y
  · exact ⟨extension x, extension_ports x, extension_rows x⟩

theorem rows_zero : rows 0 = [] := by simp [rows, edgeList, zero_list]

end
end PvNP.RealizableHardness.ActualEqualityCloud
