import PvNP.RealizableHardness.ActualBooleanOccurrenceSource
import PvNP.RealizableHardness.ActualOccurrenceCounts
import PvNP.RealizableHardness.ActualOccurrenceGapBridge
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
  · intro v hv w hw hvw
    apply List.disjoint_left.mpr
    intro x hx hy
    rcases List.mem_map.mp hx with ⟨p, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨q, _, he⟩
    exact hvw (congrArg Sigma.fst he)

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

end
end PvNP.RealizableHardness.ActualNumberedOccurrenceProducer



