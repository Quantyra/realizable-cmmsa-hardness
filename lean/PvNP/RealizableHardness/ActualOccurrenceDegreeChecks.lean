import PvNP.RealizableHardness.ActualOccurrenceDegree
/-! Uncompiled checks for actual generated original-plus-cloud degree. -/
namespace PvNP.RealizableHardness.ActualOccurrenceDegreeChecks
open ActualOccurrenceAllocation ActualOccurrenceDegree
#print axioms originalDegree_eq
#print axioms originalDegree_le_one
#print axioms internal_not_original
#print axioms original_internal_zero
#print axioms contains_tag_same
#print axioms contains_tag_other
#print axioms tagged_count_same
#print axioms tagged_count_other
#print axioms degree_eq_original_add_cloud
#print axioms port_degree_le_four
#print axioms internal_degree_exact
#print axioms degree_le_four
#print axioms degree_le_ten
#check degree_eq_original_add_cloud
#check internal_degree_exact
#check degree_le_ten
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar) : degree I x ≤ 4 := degree_le_four I x
example {N m : Nat} (I : Instance N m) (x : I.GlobalVar) : originalDegree I x ≤ 1 :=
  originalDegree_le_one I x
example {N m : Nat} (I : Instance N m) (v : Fin N)
    (e : ActualGraphEdges.Edge (I.size v)) : degree I (I.tag v (Sum.inr (e,4))) = 2 :=
  internal_degree_exact I v e 4
example {N : Nat} (I : Instance N 0) (x : I.GlobalVar) : degree I x = 0 := by
  unfold degree
  rw [Instance.zero_rows]
  rfl
end PvNP.RealizableHardness.ActualOccurrenceDegreeChecks
