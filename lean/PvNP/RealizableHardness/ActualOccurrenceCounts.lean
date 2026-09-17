import PvNP.RealizableHardness.ActualOccurrenceAllocation
import Mathlib.Data.List.ProdSigma

/-! Source-only exact enumeration, size and violation counts for the actual output.
No source-hardness, majority-gap, degree or encoded FP theorem is claimed. -/
namespace PvNP.RealizableHardness.ActualOccurrenceCounts
open ActualOccurrenceAllocation
open scoped BigOperators
set_option autoImplicit false
noncomputable section

def cloudIndices (n : Nat) : List (ActualEqualityCloud.RowId n) :=
  (ActualEqualityCloud.edgeList n).product (List.finRange 4)

theorem cloudIndices_nodup (n : Nat) : (cloudIndices n).Nodup :=
  (ActualEqualityCloud.edgeList_nodup n).product (List.nodup_finRange 4)

@[simp] theorem mem_cloudIndices {n : Nat} (q : ActualEqualityCloud.RowId n) : q ∈ cloudIndices n := by
  rcases q with ⟨e,r⟩
  simp [cloudIndices, ActualEqualityCloud.mem_edgeList]

theorem cloud_rows_eq_map (n : Nat) :
    ActualEqualityCloud.rows n = (cloudIndices n).map
      (fun q => (ActualEqualityCloud.row q, ActualEqualityCloud.rhs q)) := by
  simp [ActualEqualityCloud.rows,
    ActualEqualityCloud.row, ActualEqualityCloud.rhs, cloudIndices,
    List.product, List.map_flatMap, List.map_map, Function.comp_def]
  apply congrArg (fun f => (ActualEqualityCloud.edgeList n).flatMap f)
  funext e
  simp [ActualEqualityCloud.localRows, EqualityGadget.relabeledRows]
  rfl

end
end PvNP.RealizableHardness.ActualOccurrenceCounts

namespace PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance
open ActualOccurrenceCounts
open scoped BigOperators
set_option autoImplicit false
noncomputable section
variable {N m : Nat} (I : ActualOccurrenceAllocation.Instance N m)
local instance : DecidableEq I.RowId := Classical.decEq _

def gadgetIndices : List I.GadgetId :=
  (List.finRange N).sigma (fun v => cloudIndices (I.size v))

def rowIndices : List I.RowId :=
  (List.finRange m).map Sum.inl ++ I.gadgetIndices.map Sum.inr

theorem gadgetIndices_nodup : I.gadgetIndices.Nodup :=
  (List.nodup_finRange N).sigma (fun v => cloudIndices_nodup (I.size v))

@[simp] theorem mem_gadgetIndices (q : I.GadgetId) : q ∈ I.gadgetIndices := by
  rcases q with ⟨v,q⟩
  simp [gadgetIndices]

theorem rowIndices_nodup : I.rowIndices.Nodup := by
  apply ((List.nodup_finRange m).map Sum.inl_injective).append
    (I.gadgetIndices_nodup.map Sum.inr_injective)
  intro x hx hy
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hx
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hy
  have h : (Sum.inl r : I.RowId) = Sum.inr q := hr.trans hq.symm
  cases h

@[simp] theorem mem_rowIndices (q : I.RowId) : q ∈ I.rowIndices := by
  cases q <;> simp [rowIndices]

theorem rowIndices_toFinset : I.rowIndices.toFinset = Finset.univ := by
  ext q
  simp

/-- Equality of ordered lists, retaining the source and edge occurrence order. -/
theorem rows_eq_map : I.rows = I.rowIndices.map (fun q => (I.row q, I.rowRhs q)) := by
  simp [ActualOccurrenceAllocation.Instance.rows, ActualOccurrenceAllocation.Instance.originalRows,
    rowIndices, gadgetIndices, List.sigma, List.map_append, List.map_flatMap, List.map_map,
    List.ofFn_eq_map, ActualOccurrenceAllocation.Instance.row,
    ActualOccurrenceAllocation.Instance.rowRhs, ActualOccurrenceAllocation.Instance.tagRow,
    cloud_rows_eq_map, Function.comp_def]
  rfl

theorem rowPair_injective : Function.Injective (fun q : I.RowId => (I.row q, I.rowRhs q)) := by
  intro a b h
  by_contra hn
  have he : I.support a = I.support b := by
    rw [I.support_eq, I.support_eq]
    exact congrArg (fun f : Fin 3 → I.GlobalVar => Finset.univ.image f) (congrArg Prod.fst h)
  have hb := I.pair_intersection a b hn
  rw [he, Finset.inter_self, I.support_card] at hb
  omega

theorem rows_nodup : I.rows.Nodup := by
  rw [I.rows_eq_map]
  exact I.rowIndices_nodup.map I.rowPair_injective

def edgeCount : Nat := ∑ v : Fin N, Fintype.card (ActualGraphEdges.Edge (I.size v))

theorem rows_length : I.rows.length = m + 4 * I.edgeCount := by
  rw [I.rows_eq_map, List.length_map,
    ← List.toFinset_card_of_nodup I.rowIndices_nodup, I.rowIndices_toFinset, Finset.card_univ]
  change Fintype.card (Fin m ⊕ (Σ v : Fin N, ActualEqualityCloud.RowId (I.size v))) = _
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma,
    ActualEqualityCloud.RowId, Fintype.card_prod]
  unfold edgeCount
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simp [Nat.mul_comm]

theorem rows_length_ge : m ≤ I.rows.length := by rw [I.rows_length]; omega

theorem edge_count_bound : 2 * I.edgeCount ≤ 9 * FixedPortCycleFamily.degree * m := by
  have hc (n : Nat) : Fintype.card (ActualGraphEdges.Edge n) = (ActualGraphEdges.representatives n).card :=
    Fintype.card_subtype _
  have hb (v : Fin N) : 2 * Fintype.card (ActualGraphEdges.Edge (I.size v)) ≤
      3 * I.size v * FixedPortCycleFamily.degree := by
    rw [hc]
    exact ActualGraphEdges.representative_count_bound (I.size v)
  calc
    _ = ∑ v : Fin N, 2 * Fintype.card (ActualGraphEdges.Edge (I.size v)) := by
      rw [edgeCount, Finset.mul_sum]
    _ ≤ ∑ v : Fin N, 3 * I.size v * FixedPortCycleFamily.degree := Finset.sum_le_sum (fun v _ => hb v)
    _ = (3 * FixedPortCycleFamily.degree) * ∑ v : Fin N, I.size v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = 9 * FixedPortCycleFamily.degree * m := by rw [I.sum_sizes]; ring

theorem rows_length_le : I.rows.length ≤ (1 + 18 * FixedPortCycleFamily.degree) * m := by
  rw [I.rows_length]
  have h := I.edge_count_bound
  nlinarith

theorem rows_length_pos (hm : 0 < m) : 0 < I.rows.length := lt_of_lt_of_le hm I.rows_length_ge

def badRow (x : I.GlobalVar → ZMod 2) (q : (Fin 3 → I.GlobalVar) × ZMod 2) : Bool :=
  decide (¬ (x (q.1 0) + x (q.1 1) + x (q.1 2) = q.2))

def violations (x : I.GlobalVar → ZMod 2) : Nat := I.rows.countP (I.badRow x)
def originalViolations (x : I.GlobalVar → ZMod 2) : Nat := I.originalRows.countP (I.badRow x)
def restrictCloud (x : I.GlobalVar → ZMod 2) (v : Fin N) :
    ActualEqualityCloud.GlobalVar (I.size v) → ZMod 2 := x ∘ I.tag v

theorem badRow_tag (x : I.GlobalVar → ZMod 2) (v : Fin N)
    (q : (Fin 3 → ActualEqualityCloud.GlobalVar (I.size v)) × ZMod 2) :
    I.badRow x (I.tagRow v q) = ActualEqualityCloud.badRow (I.restrictCloud x v) q := rfl

theorem taggedCloud_violations (x : I.GlobalVar → ZMod 2) (v : Fin N) :
    ((ActualEqualityCloud.rows (I.size v)).map (I.tagRow v)).countP (I.badRow x) =
      ActualEqualityCloud.rowsViolations (I.restrictCloud x v) := by
  rw [List.countP_map]
  rfl

/-- Actual output violations split by original rows and every tagged generated cloud. -/
theorem violations_eq_original_add_clouds (x : I.GlobalVar → ZMod 2) :
    I.violations x = I.originalViolations x +
      ∑ v : Fin N, ActualEqualityCloud.rowsViolations (I.restrictCloud x v) := by
  unfold violations ActualOccurrenceAllocation.Instance.rows
  rw [List.countP_append, List.countP_flatMap]
  simp_rw [Function.comp_def, I.taggedCloud_violations]
  rw [← Fin.sum_univ_def]
  rfl

theorem violations_eq_filter_length (x : I.GlobalVar → ZMod 2) :
    I.violations x = (I.rows.filter (I.badRow x)).length := List.countP_eq_length_filter

private theorem countP_as_sum {A : Type*} (p : A → Bool) (l : List A) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]

theorem violations_eq_index_sum (x : I.GlobalVar → ZMod 2) :
    I.violations x = ∑ q : I.RowId, if I.badRow x (I.row q, I.rowRhs q) then 1 else 0 := by
  unfold violations
  rw [countP_as_sum, I.rows_eq_map, List.map_map]
  rw [← List.sum_toFinset _ I.rowIndices_nodup, I.rowIndices_toFinset]
  rfl

theorem zero_violations (J : ActualOccurrenceAllocation.Instance N 0)
    (x : J.GlobalVar → ZMod 2) : J.violations x = 0 := by
  rw [violations, J.zero_rows]
  rfl

theorem unused_cloud_violations (x : I.GlobalVar → ZMod 2) (v : Fin N) (h : I.size v = 0) :
    ActualEqualityCloud.rowsViolations (I.restrictCloud x v) = 0 := by
  unfold ActualEqualityCloud.rowsViolations
  have hz : ActualEqualityCloud.rows (I.size v) = [] := by
    rw [h]
    exact ActualEqualityCloud.rows_zero
  rw [hz]
  rfl

end
end PvNP.RealizableHardness.ActualOccurrenceAllocation.Instance
