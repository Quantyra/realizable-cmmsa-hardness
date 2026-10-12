import PvNP.RealizableHardness.ActualBooleanOccurrenceSource
import PvNP.RealizableHardness.ActualOccurrenceCounts
import PvNP.RealizableHardness.ActualOccurrenceGapBridge
import PvNP.RealizableHardness.ActualFinite3LinSource
import PvNP.RealizableHardness.ActualOccurrenceDegree
import PvNP.RealizableHardness.ActualMZOuterSourceContract
import PvNP.RealizableHardness.BooleanParityInput
import Mathlib.Tactic

/-! Exact owner-prefix numbering and row-preserving serialization of the
actual occurrence-cloud instance. This is a source-level semantic producer
candidate only; it carries no encoded-runtime or Complexity.FP certificate. -/
namespace PvNP.RealizableHardness.ActualNumberedOccurrenceProducer

open ActualOccurrenceAllocation ActualOccurrenceCounts ActualBooleanOccurrenceSource
open ActualEqualityCloud BooleanParityInput FixedPortCycleFamily

set_option autoImplicit false
noncomputable section

/-- Enumerate local ports in owner-occurrence order, followed by fresh
internal variables in representative-edge order and then Fin 5 order. -/
def localVariableList (n : Nat) : List (ActualEqualityCloud.GlobalVar n) :=
  (((List.finRange n).product (List.finRange (FixedPortCycleFamily.predecessor + 1))).map
      Sum.inl) ++
    (((ActualEqualityCloud.edgeList n).product (List.finRange 5)).map Sum.inr)

theorem localVariableList_nodup (n : Nat) : (localVariableList n).Nodup := by
  have hp : ((((List.finRange n).product
      (List.finRange (FixedPortCycleFamily.predecessor + 1))).map Sum.inl).Nodup) :=
    ((List.nodup_finRange n).product (List.nodup_finRange _)).map Sum.inl_injective
  have hi : ((((ActualEqualityCloud.edgeList n).product
      (List.finRange 5)).map Sum.inr).Nodup) :=
    ((ActualEqualityCloud.edgeList_nodup n).product (List.nodup_finRange 5)).map
      Sum.inr_injective
  apply List.Nodup.append hp hi
  apply List.disjoint_left.mpr
  intro x hx hy
  rcases List.mem_map.mp hx with ⟨p, _, rfl⟩
  rcases List.mem_map.mp hy with ⟨q, _, he⟩
  cases he

theorem localVariableList_mem (n : Nat) (x : ActualEqualityCloud.GlobalVar n) :
    x ∈ localVariableList n := by
  cases x with
  | inl p =>
      rcases p with ⟨v,j⟩
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨(v,j), List.mem_product.mpr ⟨by simp, by simp⟩, rfl⟩
  | inr p =>
      rcases p with ⟨e,t⟩
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨(e,t), List.mem_product.mpr
        ⟨ActualEqualityCloud.mem_edgeList e, by simp⟩, rfl⟩

def allocation (I : BooleanParityInput.Input) :
    ActualOccurrenceAllocation.Instance I.variables I.equations.length :=
  ActualBooleanOccurrenceSource.asInstance I

/-- The global serialization order is owner-prefix order, with each local
list retaining its port-then-representative-edge order. -/
def variableList (I : BooleanParityInput.Input) : List (allocation I).GlobalVar :=
  (List.finRange I.variables).flatMap (fun v =>
    (localVariableList ((allocation I).size v)).map ((allocation I).tag v))

theorem variableList_nodup (I : BooleanParityInput.Input) :
    (variableList I).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro v hv
    exact (localVariableList_nodup ((allocation I).size v)).map
      ((allocation I).tag v).injective
  · exact (List.nodup_finRange I.variables).imp fun {v w} hvw x hx hy => by
      rcases List.mem_map.mp hx with ⟨p, _, hpx⟩
      rcases List.mem_map.mp hy with ⟨q, _, hqx⟩
      exact hvw (congrArg Sigma.fst (hpx.trans hqx.symm))

theorem variableList_mem (I : BooleanParityInput.Input) (x : (allocation I).GlobalVar) :
    x ∈ variableList I := by
  rcases x with ⟨v,p⟩
  apply List.mem_flatMap.mpr
  exact ⟨v, by simp, List.mem_map.mpr ⟨p, localVariableList_mem ((allocation I).size v) p, rfl⟩⟩

/-- The inverse of the exact list-get enumeration is the serialized variable
index. No arbitrary equivalence chooses the output numbering. -/
def variableIndexEquiv (I : BooleanParityInput.Input) :
    (allocation I).GlobalVar ≃ Fin (variableList I).length where
  toFun x :=
    (List.Nodup.getEquiv (variableList I) (variableList_nodup I)).symm
      ⟨x, variableList_mem I x⟩
  invFun i := (List.Nodup.getEquiv (variableList I) (variableList_nodup I) i).val
  left_inv x := by simp
  right_inv i := by simp

def encodeRow (I : BooleanParityInput.Input)
    (row : (Fin 3 → (allocation I).GlobalVar) × ZMod 2) :
    BooleanParityInput.Equation (Fin (variableList I).length) :=
  ⟨variableIndexEquiv I (row.1 0), variableIndexEquiv I (row.1 1),
    variableIndexEquiv I (row.1 2), ActualOccurrenceGapBridge.bitOf row.2⟩

def outputEquations (I : BooleanParityInput.Input) :
    List (BooleanParityInput.Equation (Fin (variableList I).length)) :=
  (allocation I).rows.map (encodeRow I)

def output (I : BooleanParityInput.Input) : BooleanParityInput.Input where
  variables := (variableList I).length
  equations := outputEquations I
  nonempty := List.length_pos_iff.mp (by
    simp only [outputEquations, List.length_map]
    exact (allocation I).rows_length_pos
      (ActualBooleanOccurrenceSource.rows_positive I))

theorem output_equations (I : BooleanParityInput.Input) :
    (output I).equations = (allocation I).rows.map (encodeRow I) := rfl

/-- Pull a Boolean output assignment back to every allocated variable. -/
def pullAssignment (I : BooleanParityInput.Input)
    (a : Fin (variableList I).length → Bool) : (allocation I).GlobalVar → ZMod 2 :=
  fun x => ActualOccurrenceGapBridge.valueOf (a (variableIndexEquiv I x))

/-- Push every allocated assignment forward through the inverse of the exact
owner-prefix enumeration. -/
def pushAssignment (I : BooleanParityInput.Input)
    (x : (allocation I).GlobalVar → ZMod 2) : Fin (variableList I).length → Bool :=
  fun i => ActualOccurrenceGapBridge.bitOf (x ((variableIndexEquiv I).symm i))

def assignmentEquiv (I : BooleanParityInput.Input) :
    (Fin (variableList I).length → Bool) ≃ ((allocation I).GlobalVar → ZMod 2) where
  toFun := pullAssignment I
  invFun := pushAssignment I
  left_inv := by
    intro a
    funext i
    simp [pullAssignment, pushAssignment, ActualOccurrenceGapBridge.bitOf_valueOf]
  right_inv := by
    intro x
    funext v
    simp [pullAssignment, pushAssignment, ActualOccurrenceGapBridge.valueOf_bitOf]

theorem encodeRow_failure_eq_badRow (I : BooleanParityInput.Input)
    (a : Fin (variableList I).length → Bool)
    (row : (Fin 3 → (allocation I).GlobalVar) × ZMod 2) :
    !(BooleanParityInput.satisfied (encodeRow I row) a) =
      (allocation I).badRow (pullAssignment I a) row := by
  have hp := ActualBooleanOccurrenceSource.parity_iff
    (a (variableIndexEquiv I (row.1 0)))
    (a (variableIndexEquiv I (row.1 1)))
    (a (variableIndexEquiv I (row.1 2)))
    (ActualOccurrenceGapBridge.bitOf row.2)
  rw [ActualOccurrenceGapBridge.valueOf_bitOf] at hp
  cases hs : BooleanParityInput.satisfied (encodeRow I row) a <;>
    simp_all [BooleanParityInput.satisfied, encodeRow, pullAssignment,
      ActualOccurrenceAllocation.Instance.badRow]

theorem failureCount_eq_violations (I : BooleanParityInput.Input)
    (a : Fin (variableList I).length → Bool) :
    BooleanParityInput.failureCount (output I) a =
      (allocation I).violations (pullAssignment I a) := by
  simp [BooleanParityInput.failureCount, output, outputEquations,
    List.countP_map, encodeRow_failure_eq_badRow,
    ActualOccurrenceAllocation.Instance.violations]

theorem row_count_bound (I : BooleanParityInput.Input) :
    (output I).equations.length ≤
      (1 + 18 * FixedPortCycleFamily.degree) * I.equations.length := by
  rw [output_equations, List.length_map]
  exact (allocation I).rows_length_le


/-- The actual row list's prefix order induces its row-index equivalence.
The list is the source's original occurrences followed by the owner's
representative-edge occurrences, as certified by `rows_eq_map`. -/
theorem rowIndices_length_eq_rows_length (I : BooleanParityInput.Input) :
    (allocation I).rowIndices.length = (allocation I).rows.length := by
  rw [(allocation I).rows_eq_map]
  simp

def rowIndexEquiv (I : BooleanParityInput.Input) :
    (allocation I).RowId ≃ Fin (allocation I).rows.length :=
  (List.Nodup.getEquivOfForallMemList (allocation I).rowIndices
    (allocation I).rowIndices_nodup (allocation I).mem_rowIndices).symm.trans
      (finCongr (rowIndices_length_eq_rows_length I))

theorem rowIndexEquiv_get (I : BooleanParityInput.Input)
    (r : Fin (allocation I).rows.length) :
    (allocation I).rowIndices.get
      ((finCongr (rowIndices_length_eq_rows_length I)).symm r) =
        (rowIndexEquiv I).symm r := by
  simp [rowIndexEquiv, List.Nodup.getEquivOfForallMemList]

theorem rows_get_eq_rowIndex (I : BooleanParityInput.Input)
    (r : Fin (allocation I).rows.length) :
    (allocation I).rows.get r =
      ((allocation I).row ((rowIndexEquiv I).symm r),
        (allocation I).rowRhs ((rowIndexEquiv I).symm r)) := by
  rw [(allocation I).rows_eq_map, List.get_map]
  rw [rowIndexEquiv_get]

def finiteSource (I : BooleanParityInput.Input) :
    PvNP.RealizableHardness.Finite3LinSource
      (Fin (allocation I).rows.length) (Fin (variableList I).length) where
  row r c := variableIndexEquiv I
    ((allocation I).row ((rowIndexEquiv I).symm r) c)
  rhs r := (allocation I).rowRhs ((rowIndexEquiv I).symm r)
  row_injective := by
    intro r
    have hrow := PvNP.RealizableHardness.row_injective_of_support_card
      (allocation I).row (allocation I).support
      (allocation I).support_eq (allocation I).support_card
    intro c d h
    apply hrow
    exact (variableIndexEquiv I).injective h

theorem finiteSource_support_eq (I : BooleanParityInput.Input)
    (r : Fin (allocation I).rows.length) :
    (finiteSource I).support r =
      ((allocation I).support ((rowIndexEquiv I).symm r)).map
        (variableIndexEquiv I).toEmbedding := by
  ext x
  simp [PvNP.RealizableHardness.Finite3LinSource.support,
    ActualOccurrenceAllocation.Instance.support_eq,
    finiteSource, Equiv.apply_eq_iff_eq_symm]

theorem finiteSource_support_mem_iff_rows (I : BooleanParityInput.Input)
    (r : Fin (allocation I).rows.length) (x : Fin (variableList I).length) :
    x ∈ (finiteSource I).support r ↔
      ActualOccurrenceDegree.containsVar (allocation I)
        ((variableIndexEquiv I).symm x) ((allocation I).rows.get r) = true := by
  rw [finiteSource_support_eq, rows_get_eq_rowIndex]
  simp [ActualOccurrenceDegree.containsVar,
    ActualOccurrenceAllocation.Instance.support_eq,
    Equiv.apply_eq_iff_eq_symm]

/-- Convert an ordered list predicate count to the exact finite list-index
filter cardinality, retaining every list occurrence. -/
private theorem countP_as_sum {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, Nat.add_comm]

private theorem countP_eq_filter_card_get {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p = (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card := by
  calc
    l.countP p = (List.ofFn l.get).countP p := by rw [List.ofFn_get]
    _ = ∑ i : Fin l.length, if p (l.get i) then 1 else 0 := by
      rw [countP_as_sum, List.map_ofFn, Fin.sum_ofFn]
    _ = (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i hi
      cases p (l.get i) <;> simp

theorem finiteSource_degree_ten (I : BooleanParityInput.Input)
    (x : Fin (variableList I).length) :
    (Finset.univ.filter fun r : Fin (allocation I).rows.length =>
      x ∈ (finiteSource I).support r).card ≤ 10 := by
  have hf : (Finset.univ.filter fun r : Fin (allocation I).rows.length =>
      x ∈ (finiteSource I).support r) =
      Finset.univ.filter (fun r =>
        ActualOccurrenceDegree.containsVar (allocation I)
          ((variableIndexEquiv I).symm x) ((allocation I).rows.get r) = true) := by
    ext r
    simp [finiteSource_support_mem_iff_rows]
  rw [hf, ← countP_eq_filter_card_get]
  exact ActualOccurrenceDegree.degree_le_ten (allocation I) ((variableIndexEquiv I).symm x)

theorem finiteSource_overlap_one (I : BooleanParityInput.Input)
    (r s : Fin (allocation I).rows.length) (h : r ≠ s) :
    ((finiteSource I).support r ∩ (finiteSource I).support s).card ≤ 1 := by
  rw [finiteSource_support_eq, finiteSource_support_eq]
  let e := (variableIndexEquiv I).toEmbedding
  have hmap (A B : Finset (allocation I).GlobalVar) :
      A.map e ∩ B.map e = (A ∩ B).map e := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_map]
    constructor
    · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
      have hab : a = b := e.injective (hax.trans hbx.symm)
      subst b
      exact ⟨a, ⟨ha, hb⟩, hax⟩
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨a, hb, rfl⟩⟩
  rw [hmap, Finset.card_map]
  apply (allocation I).pair_intersection
  intro hq
  apply h
  exact congrArg (rowIndexEquiv I) hq

def encoded3Lin (I : BooleanParityInput.Input) :
    ActualMZOuterSourceContract.Encoded3Lin where
  vars := (variableList I).length
  rows := (allocation I).rows.length
  rows_pos := (allocation I).rows_length_pos
    (ActualBooleanOccurrenceSource.rows_positive I)
  source := finiteSource I
  degree_ten := finiteSource_degree_ten I
  overlap_one := finiteSource_overlap_one I

theorem finiteSource_violations_eq_allocation (I : BooleanParityInput.Input)
    (a : Fin (variableList I).length → Bool) :
    (finiteSource I).violations
      (fun v => ActualOccurrenceGapBridge.valueOf (a v)) =
      (allocation I).violations (pullAssignment I a) := by
  unfold PvNP.RealizableHardness.Finite3LinSource.violations
    ActualOccurrenceAllocation.Instance.violations
  rw [countP_eq_filter_card_get, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro r _
  rw [rows_get_eq_rowIndex]
  simp [PvNP.RealizableHardness.Finite3LinSource.badRow,
    ActualOccurrenceAllocation.Instance.badRow, finiteSource, pullAssignment]

theorem encoded3Lin_failureCount_eq_violations (I : BooleanParityInput.Input)
    (a : Fin (variableList I).length → Bool) :
    (encoded3Lin I).source.violations
      (fun v => ActualOccurrenceGapBridge.valueOf (a v)) =
      BooleanParityInput.failureCount (output I) a := by
  rw [encoded3Lin, finiteSource_violations_eq_allocation,
    failureCount_eq_violations]

theorem variableList_length_eq_cardinality (I : BooleanParityInput.Input) :
    (variableList I).length = Fintype.card ((allocation I).GlobalVar) := by
  have htoFinset : (variableList I).toFinset = Finset.univ := by
    ext x
    simp [variableList_mem]
  rw [← List.toFinset_card_of_nodup (variableList_nodup I), htoFinset, Finset.card_univ]

theorem variable_count_eq (I : BooleanParityInput.Input) :
    (output I).variables =
      3 * FixedPortCycleFamily.degree * I.equations.length +
        5 * (allocation I).edgeCount := by
  rw [output, variableList_length_eq_cardinality]
  simp only [ActualOccurrenceAllocation.Instance.GlobalVar,
    ActualEqualityCloud.GlobalVar, ActualGraphEdges.Vertex,
    PortCycleReplacement.Port, Fintype.card_sigma, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  rw [FixedPortCycleFamily.degree_eq]
  calc
    (∑ v : Fin I.variables,
        (allocation I).size v * (FixedPortCycleFamily.predecessor + 1) +
          Fintype.card (ActualGraphEdges.Edge ((allocation I).size v)) * 5) =
        (∑ v : Fin I.variables, (allocation I).size v) *
          (FixedPortCycleFamily.predecessor + 1) +
          5 * (∑ v : Fin I.variables,
            Fintype.card (ActualGraphEdges.Edge ((allocation I).size v))) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      ring
    _ = 3 * (FixedPortCycleFamily.predecessor + 1) * I.equations.length +
          5 * (allocation I).edgeCount := by
      rw [(allocation I).sum_sizes]
      unfold ActualOccurrenceAllocation.Instance.edgeCount
      ring

theorem variable_count_bound (I : BooleanParityInput.Input) :
    2 * (encoded3Lin I).vars ≤
      51 * FixedPortCycleFamily.degree * I.equations.length := by
  change 2 * (output I).variables ≤
    51 * FixedPortCycleFamily.degree * I.equations.length
  rw [variable_count_eq]
  have he := (allocation I).edge_count_bound
  nlinarith [he]


theorem output_inputWords (I : BooleanParityInput.Input) :
    BooleanParityInput.inputWords (output I) =
      [ (variableList I).length, (allocation I).rows.length ] ++
        (allocation I).rows.flatMap (fun row =>
          [variableIndexEquiv I (row.1 0), variableIndexEquiv I (row.1 1),
            variableIndexEquiv I (row.1 2),
            if ActualOccurrenceGapBridge.bitOf row.2 then 1 else 0]) := by
  simp [BooleanParityInput.inputWords, BooleanParityInput.equationWords,
    output, outputEquations, encodeRow]

end
end PvNP.RealizableHardness.ActualNumberedOccurrenceProducer