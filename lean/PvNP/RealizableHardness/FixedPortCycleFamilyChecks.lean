import PvNP.RealizableHardness.FixedPortCycleFamily
/-! Source-only checks. No kernel acceptance or profile output is claimed. -/
open PvNP.RealizableHardness.FixedPortCycleFamily

#print axioms degree_eq
#print axioms baseRotation_involutive
#print axioms base_spectral
#print axioms baseRotation_spectral
#print axioms graph_degree
#print axioms graph_order
#print axioms boundary_eq_cut
#print axioms kappa_pos
#print axioms cut_expansion
#print axioms boundary_expansion
#print axioms table_length
#print axioms baseRotation_values

set_option pp.fullNames true in
#check boundary_expansion
set_option pp.fullNames true in
#check baseRotation_values

example : (graph 0).order = 0 := by simp [graph_order]
example : (graph 1).order = degree := by simp [graph_order]
example : (graph 2).deg = 3 := graph_degree 2
example : (table 0).length = 0 := by simp [table_length]
example : (table 1).length = degree * 3 := by simp [table_length]
example : 0 < kappa := kappa_pos
