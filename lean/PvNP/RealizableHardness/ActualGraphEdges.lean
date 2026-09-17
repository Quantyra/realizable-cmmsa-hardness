import PvNP.RealizableHardness.FixedPortCycleFamily
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-! Source-only representative construction for the actual fixed graph.
No simple-graph quotient: parallel edges retain their distinct dart orbits. -/
namespace PvNP.RealizableHardness.ActualGraphEdges
open PortCycleReplacement
set_option autoImplicit false
noncomputable section

abbrev Vertex (n : Nat) := Port n FixedPortCycleFamily.predecessor
abbrev Dart (n : Nat) := Vertex n × Fin 3

def reverse {n : Nat} (d : Dart n) : Dart n :=
  rotation (FixedPortCycleFamily.baseRotation n) d

@[simp] theorem reverse_reverse {n : Nat} (d : Dart n) : reverse (reverse d) = d :=
  rotation_involutive _ (FixedPortCycleFamily.baseRotation_involutive n) d

theorem reverse_injective (n : Nat) : Function.Injective (@reverse n) :=
  Function.Involutive.injective reverse_reverse

/-- A total numeric order on the actual (vertex,port) pair. -/
def rank {n : Nat} (v : Vertex n) : Nat := (finProdFinEquiv v).val

theorem rank_injective (n : Nat) : Function.Injective (@rank n) := by
  intro u v h
  apply finProdFinEquiv.injective
  exact Fin.val_injective h

def Nonloop {n : Nat} (d : Dart n) : Prop := d.1 ≠ (reverse d).1
def IsRep {n : Nat} (d : Dart n) : Prop := rank d.1 < rank (reverse d).1

instance {n : Nat} (d : Dart n) : Decidable (Nonloop d) := inferInstanceAs (Decidable (_ ≠ _))
instance {n : Nat} (d : Dart n) : Decidable (IsRep d) := inferInstanceAs (Decidable (_ < _))

theorem rep_nonloop {n : Nat} {d : Dart n} (h : IsRep d) : Nonloop d := by
  intro he
  unfold IsRep at h
  rw [he] at h
  exact (Nat.lt_irrefl _ h)

theorem rep_reverse_excluded {n : Nat} {d : Dart n} (h : IsRep d) : ¬ IsRep (reverse d) := by
  simpa only [IsRep, reverse_reverse] using Nat.not_lt_of_gt h

theorem nonloop_reverse {n : Nat} {d : Dart n} (h : Nonloop d) : Nonloop (reverse d) := by
  simpa only [Nonloop, reverse_reverse, ne_eq, eq_comm] using h

/-- Exactly one dart of every nonloop two-dart orbit is selected. -/
theorem exactly_one {n : Nat} {d : Dart n} (h : Nonloop d) :
    (IsRep d ∨ IsRep (reverse d)) ∧ ¬ (IsRep d ∧ IsRep (reverse d)) := by
  have hn : rank d.1 ≠ rank (reverse d).1 := fun he => h (rank_injective n he)
  constructor
  · simpa only [IsRep, reverse_reverse] using lt_or_gt_of_ne hn
  · rintro ⟨ha, hb⟩
    exact rep_reverse_excluded ha hb

def canonical {n : Nat} (d : Dart n) : Dart n := if IsRep d then d else reverse d

theorem canonical_rep {n : Nat} {d : Dart n} (h : Nonloop d) : IsRep (canonical d) := by
  rcases (exactly_one h).1 with hd | hr
  · simp [canonical, hd]
  · have hn : ¬ IsRep d := by simpa using rep_reverse_excluded hr
    simp [canonical, hn, hr]

theorem canonical_of_rep {n : Nat} {d : Dart n} (h : IsRep d) : canonical d = d := by
  simp [canonical, h]

theorem canonical_reverse {n : Nat} {d : Dart n} (h : Nonloop d) :
    canonical (reverse d) = canonical d := by
  rcases (exactly_one h).1 with hd | hr
  · simp [canonical, hd, rep_reverse_excluded hd]
  · have hn : ¬ IsRep d := by simpa using rep_reverse_excluded hr
    simp [canonical, hr, hn]

/-- Orbit identity is equality of darts or reversal, never equality of endpoints alone. -/
theorem rep_orbit_unique {n : Nat} {a b : Dart n} (ha : IsRep a) (hb : IsRep b)
    (h : a = b ∨ a = reverse b) : a = b := by
  rcases h with h | h
  · exact h
  · subst a
    exact False.elim (rep_reverse_excluded hb ha)

def dartList (n : Nat) : List (Dart n) :=
  ((List.finRange n).product (List.finRange (FixedPortCycleFamily.predecessor + 1))).product
    (List.finRange 3)

theorem dartList_nodup (n : Nat) : (dartList n).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange _)).product (List.nodup_finRange 3)

@[simp] theorem mem_dartList {n : Nat} (d : Dart n) : d ∈ dartList n := by
  rcases d with ⟨⟨v, j⟩, i⟩
  simp [dartList, List.product]

/-- This is precisely the source-dart order of the already constructed typed table. -/
theorem dartList_eq_table_sources (n : Nat) :
    dartList n = (FixedPortCycleFamily.table n).map Prod.fst := by
  simp [dartList, FixedPortCycleFamily.table, PortCycleReplacement.table,
    List.product, List.map_flatMap, List.flatMap_assoc, List.flatMap_map,
    List.map_map, Function.comp_def]

def representativeList (n : Nat) : List (Dart n) := (dartList n).filter (fun d => decide (IsRep d))
def representatives (n : Nat) : Finset (Dart n) := Finset.univ.filter IsRep
abbrev Edge (n : Nat) := {d : Dart n // IsRep d}

/-- Required before embedding the gadget's two distinct terminal variables. -/
theorem edge_terminals_distinct {n : Nat} (e : Edge n) : e.val.1 ≠ (reverse e.val).1 :=
  rep_nonloop e.property

theorem loop_never_crosses {n : Nat} (S : Vertex n → Bool) (d : Dart n)
    (h : d.1 = (reverse d).1) : S d.1 = S (reverse d).1 := congrArg S h

@[simp] theorem mem_representatives {n : Nat} {d : Dart n} :
    d ∈ representatives n ↔ IsRep d := by simp [representatives]

@[simp] theorem mem_representativeList {n : Nat} {d : Dart n} :
    d ∈ representativeList n ↔ IsRep d := by simp [representativeList]

theorem representativeList_nodup (n : Nat) : (representativeList n).Nodup :=
  (dartList_nodup n).filter _

theorem representativeList_toFinset (n : Nat) :
    (representativeList n).toFinset = representatives n := by
  ext d
  simp

theorem representativeList_length (n : Nat) :
    (representativeList n).length = (representatives n).card := by
  rw [← representativeList_toFinset]
  exact (List.toFinset_card_of_nodup (representativeList_nodup n)).symm

/-- Reversal supplies a disjoint second dart for every representative. -/
theorem representative_count_bound (n : Nat) :
    2 * (representatives n).card ≤ 3 * n * FixedPortCycleFamily.degree := by
  let r := representatives n
  have hd : Disjoint r (r.image reverse) := by
    apply Finset.disjoint_left.mpr
    intro d hd hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact rep_reverse_excluded (mem_representatives.mp he) (mem_representatives.mp hd)
  have hc : (r.image reverse).card = r.card := Finset.card_image_of_injective r (reverse_injective n)
  have hu : (r ∪ r.image reverse).card ≤ Fintype.card (Dart n) := Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint hd, hc] at hu
  have ht : Fintype.card (Dart n) = n * FixedPortCycleFamily.degree * 3 := by
    simp [Dart, Vertex, Port, Fintype.card_prod, ← FixedPortCycleFamily.degree_eq]
  rw [ht] at hu
  dsimp [r] at hu
  nlinarith

def crossing (n : Nat) (S : Vertex n → Bool) : Finset (Dart n) :=
  (representatives n).filter fun d => S d.1 ≠ S (reverse d).1

def outgoing (n : Nat) (S : Vertex n → Bool) : Finset (Dart n) :=
  Finset.univ.filter fun d => S d.1 = true ∧ S (reverse d).1 = false

def orient {n : Nat} (S : Vertex n → Bool) (d : Dart n) : Dart n :=
  if S d.1 then d else reverse d

theorem outgoing_nonloop {n : Nat} {S : Vertex n → Bool} {d : Dart n}
    (h : d ∈ outgoing n S) : Nonloop d := by
  obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp h).2
  intro he
  rw [he, ht] at hs
  contradiction

theorem orient_crossing {n : Nat} {S : Vertex n → Bool} {d : Dart n}
    (h : S d.1 ≠ S (reverse d).1) : orient S d ∈ outgoing n S := by
  cases hs : S d.1 <;> cases ht : S (reverse d).1 <;>
    simp_all [orient, outgoing]

theorem canonical_orient {n : Nat} {S : Vertex n → Bool} {d : Dart n}
    (hd : IsRep d) : canonical (orient S d) = d := by
  unfold orient
  split
  · exact canonical_of_rep hd
  · rw [canonical_reverse (rep_nonloop hd), canonical_of_rep hd]

theorem canonical_crossing {n : Nat} {S : Vertex n → Bool} {d : Dart n}
    (hd : d ∈ outgoing n S) : canonical d ∈ crossing n S := by
  have hr := canonical_rep (outgoing_nonloop hd)
  obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp hd).2
  apply Finset.mem_filter.mpr
  refine ⟨mem_representatives.mpr hr, ?_⟩
  by_cases h : IsRep d <;> simp [canonical, h, hs, ht]

theorem orient_canonical {n : Nat} {S : Vertex n → Bool} {d : Dart n}
    (hd : d ∈ outgoing n S) : orient S (canonical d) = d := by
  obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp hd).2
  by_cases h : IsRep d <;> simp [canonical, orient, h, hs, ht]

/-- Actual explicit bijection: orient a crossing representative from S to its complement. -/
theorem crossing_card_eq_outgoing (n : Nat) (S : Vertex n → Bool) :
    (crossing n S).card = (outgoing n S).card := by
  apply Finset.card_bij (fun d _ => orient S d)
  · intro d hd
    exact orient_crossing (Finset.mem_filter.mp hd).2
  · intro a ha b hb he
    have h := congrArg (@canonical n) he
    rw [canonical_orient (mem_representatives.mp (Finset.mem_filter.mp ha).1),
      canonical_orient (mem_representatives.mp (Finset.mem_filter.mp hb).1)] at h
    exact h
  · intro d hd
    exact ⟨canonical d, canonical_crossing hd, orient_canonical hd⟩

theorem outgoing_eq_actual_darts (n : Nat) (S : Vertex n → Bool) :
    outgoing n S = (FixedPortCycleFamily.graph n).dartsBetween
      (ExpanderCutInstantiation.support (FixedPortCycleFamily.graph n) S)
      (ExpanderCutInstantiation.support (FixedPortCycleFamily.graph n) S)ᶜ := by
  ext d
  simp only [outgoing, Complexity.RegGraph.dartsBetween, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_compl, ExpanderCutInstantiation.support]
  change (S d.1 = true ∧ S (reverse d).1 = false) ↔
    d ∈ Finset.univ.filter (fun x : Dart n => S x.1 = true ∧ ¬ S (reverse x).1 = true)
  simp only [Finset.mem_filter]
  cases S (reverse d).1 <;> simp
  intro _
  exact Finset.mem_univ d

/-- The selected edge count is the accepted actual graph cut, with all multiplicities. -/
theorem crossing_card_eq_cut (n : Nat) (S : Vertex n → Bool) :
    ((crossing n S).card : Real) = FixedPortCycleFamily.cut n S := by
  rw [crossing_card_eq_outgoing]
  have hb := ExpanderCutInstantiation.boundary_eq_outgoing (FixedPortCycleFamily.graph n) S
  rw [FixedPortCycleFamily.boundary_eq_cut n S] at hb
  have ho := congrArg (fun t : Finset (Dart n) => (t.card : Real))
    (outgoing_eq_actual_darts n S)
  exact ho.trans hb.symm

theorem crossing_expansion (n : Nat) (S : Vertex n → Bool) :
    FixedPortCycleFamily.kappa * smallSide S ≤ ((crossing n S).card : Real) := by
  rw [crossing_card_eq_cut]
  exact FixedPortCycleFamily.cut_expansion n S

theorem zero_representatives : representatives 0 = ∅ := by
  ext d
  exact Fin.elim0 d.1.1

theorem zero_list : representativeList 0 = [] := by simp [representativeList, dartList]

end
end PvNP.RealizableHardness.ActualGraphEdges
