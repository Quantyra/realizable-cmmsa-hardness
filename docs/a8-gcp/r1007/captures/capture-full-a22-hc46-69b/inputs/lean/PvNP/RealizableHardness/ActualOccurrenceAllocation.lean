import PvNP.RealizableHardness.ActualEqualityCloud
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.BigOperators

/-! Source-only ordered occurrence allocation and original-plus-cloud rows.
The source may repeat an owner within a row. Output row variables are distinct
occurrence anchors; the fixed gadget's unique-port property controls intersections. -/
namespace PvNP.RealizableHardness.ActualOccurrenceAllocation
open scoped BigOperators
set_option autoImplicit false
noncomputable section

structure Instance (N m : Nat) where
  vars : Fin m → Fin 3 → Fin N
  rhs : Fin m → ZMod 2

abbrev Slot (m : Nat) := Fin m × Fin 3
def slotList (m : Nat) : List (Slot m) := (List.finRange m).product (List.finRange 3)

theorem slotList_nodup (m : Nat) : (slotList m).Nodup :=
  (List.nodup_finRange m).product (List.nodup_finRange 3)

@[simp] theorem mem_slotList {m : Nat} (o : Slot m) : o ∈ slotList m := by
  rcases o with ⟨r,i⟩
  simp [slotList, List.product]

namespace Instance
variable {N m : Nat} (I : Instance N m)

def owner (o : Slot m) : Fin N := I.vars o.1 o.2
abbrev Occ (v : Fin N) := {o : Slot m // I.owner o = v}
def occurrenceList (v : Fin N) : List (Slot m) :=
  (slotList m).filter (fun o => decide (I.owner o = v))
def size (v : Fin N) : Nat := (I.occurrenceList v).length

@[simp] theorem mem_occurrenceList (v : Fin N) (o : Slot m) :
    o ∈ I.occurrenceList v ↔ I.owner o = v := by simp [occurrenceList]

theorem occurrenceList_nodup (v : Fin N) : (I.occurrenceList v).Nodup :=
  (slotList_nodup m).filter _

def occurrenceMembership (v : Fin N) : I.Occ v ≃ {o // o ∈ I.occurrenceList v} where
  toFun o := ⟨o.val, (I.mem_occurrenceList v o.val).mpr o.property⟩
  invFun o := ⟨o.val, (I.mem_occurrenceList v o.val).mp o.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ordinal is derived from the actual filtered list's get/idxOf equivalence. -/
def ordinal (v : Fin N) : I.Occ v ≃ Fin (I.size v) :=
  (I.occurrenceMembership v).trans
    (List.Nodup.getEquiv (I.occurrenceList v) (I.occurrenceList_nodup v)).symm

theorem ordinal_get (v : Fin N) (o : I.Occ v) :
    (I.occurrenceList v).get (I.ordinal v o) = o.val := by
  have h := (List.Nodup.getEquiv (I.occurrenceList v) (I.occurrenceList_nodup v)).apply_symm_apply
    (I.occurrenceMembership v o)
  exact congrArg Subtype.val h

theorem occurrence_card (v : Fin N) : Fintype.card (I.Occ v) = I.size v := by
  simpa using Fintype.card_congr (I.ordinal v)

def occurrencePartition : (Σ v : Fin N, I.Occ v) ≃ Slot m where
  toFun q := q.2.val
  invFun o := ⟨I.owner o, ⟨o,rfl⟩⟩
  left_inv := by
    rintro ⟨v,o,ho⟩
    cases ho
    rfl
  right_inv _ := rfl

theorem sum_sizes : (∑ v : Fin N, I.size v) = 3 * m := by
  calc
    _ = ∑ v : Fin N, Fintype.card (I.Occ v) :=
      Finset.sum_congr rfl (fun v _ => (I.occurrence_card v).symm)
    _ = Fintype.card (Σ v : Fin N, I.Occ v) := by rw [Fintype.card_sigma]
    _ = Fintype.card (Slot m) := Fintype.card_congr I.occurrencePartition
    _ = 3 * m := by simp [Slot, Fintype.card_prod, Nat.mul_comm]

abbrev GlobalVar := Σ v : Fin N, ActualEqualityCloud.GlobalVar (I.size v)
abbrev GadgetId := Σ v : Fin N, ActualEqualityCloud.RowId (I.size v)
abbrev RowId := Fin m ⊕ I.GadgetId

def tag (v : Fin N) : ActualEqualityCloud.GlobalVar (I.size v) ↪ I.GlobalVar where
  toFun x := ⟨v,x⟩
  inj' := by intro a b h; cases h; rfl

/-- Each occurrence uses its own ordinal at port zero, leaving other ports unanchored. -/
def anchor (o : Slot m) : I.GlobalVar :=
  ⟨I.owner o, Sum.inl (I.ordinal (I.owner o) ⟨o,rfl⟩, 0)⟩

def recover : I.GlobalVar → Option (Slot m)
  | ⟨v, Sum.inl p⟩ => some ((I.ordinal v).symm p.1).val
  | ⟨_, Sum.inr _⟩ => none

theorem recover_anchor (o : Slot m) : I.recover (I.anchor o) = some o := by
  simp [recover, anchor]

theorem anchor_injective : Function.Injective I.anchor := by
  intro a b h
  have he := congrArg I.recover h
  simpa only [I.recover_anchor, Option.some.injEq] using he

theorem anchor_owner (o : Slot m) : (I.anchor o).1 = I.owner o := rfl

def originalRow (r : Fin m) (i : Fin 3) : I.GlobalVar := I.anchor (r,i)
def originalSupport (r : Fin m) : Finset I.GlobalVar := Finset.univ.image (I.originalRow r)
def gadgetRow (q : I.GadgetId) (i : Fin 3) : I.GlobalVar := I.tag q.1 (ActualEqualityCloud.row q.2 i)
def gadgetSupport (q : I.GadgetId) : Finset I.GlobalVar :=
  (ActualEqualityCloud.support q.2).map (I.tag q.1)

theorem originalRow_injective (r : Fin m) : Function.Injective (I.originalRow r) := by
  intro i j h
  exact congrArg Prod.snd (I.anchor_injective h)

theorem original_disjoint (r s : Fin m) (h : r ≠ s) :
    Disjoint (I.originalSupport r) (I.originalSupport s) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
  exact h (congrArg Prod.fst (I.anchor_injective (hi.trans hj.symm)))

theorem gadget_member_owner (q : I.GadgetId) (x : I.GlobalVar)
    (hx : x ∈ I.gadgetSupport q) : x.1 = q.1 := by
  obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
  exact (congrArg Sigma.fst hy).symm

theorem gadget_support_card (q : I.GadgetId) : (I.gadgetSupport q).card = 3 := by
  rw [gadgetSupport, Finset.card_map]
  exact ActualEqualityCloud.support_card q.2

theorem gadgetSupport_eq (q : I.GadgetId) :
    I.gadgetSupport q = Finset.univ.image (I.gadgetRow q) := by
  ext x
  simp [gadgetSupport, ActualEqualityCloud.support_eq, gadgetRow,
    Finset.mem_map, Finset.mem_image]

theorem original_support_card (r : Fin m) : (I.originalSupport r).card = 3 := by
  rw [originalSupport, Finset.card_image_of_injective _ (I.originalRow_injective r)]
  simp

theorem different_clouds_disjoint (q t : I.GadgetId) (h : q.1 ≠ t.1) :
    Disjoint (I.gadgetSupport q) (I.gadgetSupport t) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h ((I.gadget_member_owner q x hx).symm.trans (I.gadget_member_owner t x hy))

/-- Each concrete gadget row has at most one port, independent of source owner collisions. -/
theorem cloud_support_port_unique {n : Nat} (q : ActualEqualityCloud.RowId n)
    (p t : ActualGraphEdges.Vertex n)
    (hp : Sum.inl p ∈ ActualEqualityCloud.support q)
    (ht : Sum.inl t ∈ ActualEqualityCloud.support q) : p = t := by
  change Sum.inl p ∈ (EqualityGadget.support q.2).map
    (ActualEqualityCloud.embedding q.1) at hp
  change Sum.inl t ∈ (EqualityGadget.support q.2).map
    (ActualEqualityCloud.embedding q.1) at ht
  obtain ⟨u, hu, hup⟩ := Finset.mem_map.mp hp
  obtain ⟨v, hv, hvt⟩ := Finset.mem_map.mp ht
  have hut : u < 2 := by
    fin_cases u <;> simp_all [ActualEqualityCloud.embedding, ActualEqualityCloud.embedFn]
  have hvt' : v < 2 := by
    fin_cases v <;> simp_all [ActualEqualityCloud.embedding, ActualEqualityCloud.embedFn]
  have huv := ActualEqualityCloud.local_terminal_unique q.2 u hu v hv hut hvt'
  have he : (Sum.inl p : ActualEqualityCloud.GlobalVar n) = Sum.inl t :=
    hup.symm.trans ((congrArg (ActualEqualityCloud.embedding q.1) huv).trans hvt)
  exact Sum.inl.inj he

/-- The actual recovery discriminator excludes internals without assuming distinct owners. -/
theorem gadget_recoverable_unique (q : I.GadgetId) (x y : I.GlobalVar)
    (hx : x ∈ I.gadgetSupport q) (hy : y ∈ I.gadgetSupport q)
    (hxp : I.recover x ≠ none) (hyp : I.recover y ≠ none) : x = y := by
  obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb, hby⟩ := Finset.mem_map.mp hy
  subst x
  subst y
  cases a with
  | inl p =>
    cases b with
    | inl t =>
      exact congrArg (I.tag q.1) (congrArg Sum.inl (cloud_support_port_unique q.2 p t ha hb))
    | inr z => exact (hyp rfl).elim
  | inr z => exact (hxp rfl).elim

/-- Original positions have distinct anchors even when their source owners coincide. -/
theorem original_gadget_intersection (r : Fin m) (q : I.GadgetId) :
    (I.originalSupport r ∩ I.gadgetSupport q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).1
  have hxp : I.recover x ≠ none := by
    rw [← hi]
    change I.recover (I.anchor (r,i)) ≠ none
    rw [I.recover_anchor]
    simp
  have hyp : I.recover y ≠ none := by
    rw [← hj]
    change I.recover (I.anchor (r,j)) ≠ none
    rw [I.recover_anchor]
    simp
  exact I.gadget_recoverable_unique q x y
    (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2 hxp hyp

theorem gadget_pair_intersection (q t : I.GadgetId) (h : q ≠ t) :
    (I.gadgetSupport q ∩ I.gadgetSupport t).card ≤ 1 := by
  rcases q with ⟨v,a⟩
  rcases t with ⟨w,b⟩
  by_cases hv : v = w
  · subst w
    have hab : a ≠ b := fun he => h (congrArg (Sigma.mk v) he)
    simpa only [gadgetSupport, ← Finset.map_inter, Finset.card_map]
      using ActualEqualityCloud.pair_intersection a b hab
  · have hd := I.different_clouds_disjoint ⟨v,a⟩ ⟨w,b⟩ hv
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
    simp

def row : I.RowId → Fin 3 → I.GlobalVar
  | Sum.inl r => I.originalRow r
  | Sum.inr q => I.gadgetRow q

def rowRhs : I.RowId → ZMod 2
  | Sum.inl r => I.rhs r
  | Sum.inr q => ActualEqualityCloud.rhs q.2

def support : I.RowId → Finset I.GlobalVar
  | Sum.inl r => I.originalSupport r
  | Sum.inr q => I.gadgetSupport q

theorem support_eq (q : I.RowId) : I.support q = Finset.univ.image (I.row q) := by
  cases q with
  | inl r => rfl
  | inr q => exact I.gadgetSupport_eq q

theorem support_card (q : I.RowId) : (I.support q).card = 3 := by
  cases q with
  | inl r => exact I.original_support_card r
  | inr q => exact I.gadget_support_card q

theorem pair_intersection (a b : I.RowId) (h : a ≠ b) :
    (I.support a ∩ I.support b).card ≤ 1 := by
  cases a with
  | inl r =>
    cases b with
    | inl s =>
      have hrs : r ≠ s := fun he => h (congrArg Sum.inl he)
      change (I.originalSupport r ∩ I.originalSupport s).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (I.original_disjoint r s hrs)]
      simp
    | inr q => exact I.original_gadget_intersection r q
  | inr q =>
    cases b with
    | inl r =>
      simpa only [support, Finset.inter_comm] using I.original_gadget_intersection r q
    | inr t =>
      exact I.gadget_pair_intersection q t (fun he => h (congrArg Sum.inr he))

def originalRows : List ((Fin 3 → I.GlobalVar) × ZMod 2) :=
  List.ofFn (fun r : Fin m => (I.originalRow r, I.rhs r))

def tagRow (v : Fin N)
    (q : (Fin 3 → ActualEqualityCloud.GlobalVar (I.size v)) × ZMod 2) :
      (Fin 3 → I.GlobalVar) × ZMod 2 := (I.tag v ∘ q.1, q.2)

/-- Original equation occurrences first, then clouds in variable order, preserving local order. -/
def rows : List ((Fin 3 → I.GlobalVar) × ZMod 2) :=
  I.originalRows ++ (List.finRange N).flatMap (fun v =>
    (ActualEqualityCloud.rows (I.size v)).map (I.tagRow v))

theorem row_mem_rows (q : I.RowId) : (I.row q, I.rowRhs q) ∈ I.rows := by
  cases q with
  | inl r =>
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨r,rfl⟩
  | inr q =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨q.1, by simp, ?_⟩
    apply List.mem_map.mpr
    refine ⟨(ActualEqualityCloud.row q.2, ActualEqualityCloud.rhs q.2), ?_, rfl⟩
    exact ActualEqualityCloud.row_mem_rows q.2.1 q.2.2

private theorem local_row_of_mem {n : Nat}
    (t : (Fin 3 → ActualEqualityCloud.GlobalVar n) × ZMod 2)
    (h : t ∈ ActualEqualityCloud.rows n) :
    ∃ q : ActualEqualityCloud.RowId n, (ActualEqualityCloud.row q, ActualEqualityCloud.rhs q) = t := by
  obtain ⟨e, _, he⟩ := List.mem_flatMap.mp h
  rw [ActualEqualityCloud.localRows_eq] at he
  obtain ⟨r, hr⟩ := List.mem_ofFn.mp he
  exact ⟨(e,r),hr⟩

/-- Conversely, every generated equation is one of the explicit row occurrences. -/
theorem rows_mem_iff (t : (Fin 3 → I.GlobalVar) × ZMod 2) :
    t ∈ I.rows ↔ ∃ q : I.RowId, (I.row q, I.rowRhs q) = t := by
  constructor
  · intro ht
    rcases List.mem_append.mp ht with ho | hg
    · obtain ⟨r, hr⟩ := List.mem_ofFn.mp ho
      exact ⟨Sum.inl r,hr⟩
    · obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hg
      obtain ⟨u, hu, hut⟩ := List.mem_map.mp hv
      obtain ⟨q, hq⟩ := local_row_of_mem u hu
      refine ⟨Sum.inr ⟨v,q⟩, ?_⟩
      exact (congrArg (I.tagRow v) hq).trans hut
  · rintro ⟨q,rfl⟩
    exact I.row_mem_rows q

theorem zero_size (J : Instance N 0) (v : Fin N) : J.size v = 0 := by
  simp [size, occurrenceList, slotList, List.product]

theorem zero_rows (J : Instance N 0) : J.rows = [] := by
  simp [rows, originalRows]
  intro v
  rw [zero_size J v]
  exact ActualEqualityCloud.rows_zero

end Instance
end
end PvNP.RealizableHardness.ActualOccurrenceAllocation
