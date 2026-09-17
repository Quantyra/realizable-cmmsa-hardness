import PvNP.RealizableHardness.ActualEqualityCloudDegree

/-! Uncompiled source checks. -/
namespace PvNP.RealizableHardness.ActualEqualityCloudDegreeChecks
open ActualGraphEdges ActualEqualityCloud ActualEqualityCloudDegree

#print axioms local_count
#print axioms degree_eq_sum
#print axioms port_outside
#print axioms local_port_degree
#print axioms port_degree_eq_incidence
#print axioms port_degree_le_three
#print axioms internal_outside
#print axioms local_internal_degree
#print axioms internal_degree_exact
#print axioms localRows_length
#print axioms rows_length

#check port_degree_eq_incidence
#check internal_degree_exact
#check rows_length

example {n : Nat} (p : Vertex n) : degree (Sum.inl p) ≤ 3 := port_degree_le_three p
example {n : Nat} (e : Edge n) : degree (Sum.inr (e,0)) = 2 := internal_degree_exact e 0
example {n : Nat} (e : Edge n) : degree (Sum.inr (e,4)) = 2 := internal_degree_exact e 4
example : (rows 0).length = 0 := by rw [rows_zero]; rfl
example {n : Nat} (e f : Edge n) (h : e ≠ f) :
    Sum.inr (e,0) ∉ Set.range (embedding f) := internal_outside e f 0 h

end PvNP.RealizableHardness.ActualEqualityCloudDegreeChecks
