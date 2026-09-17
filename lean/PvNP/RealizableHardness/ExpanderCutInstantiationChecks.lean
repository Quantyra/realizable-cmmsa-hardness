import PvNP.RealizableHardness.ExpanderCutInstantiation
/-! Source-only checks: no compilation or axiom acceptance claimed. -/
open PvNP.RealizableHardness.ExpanderCutInstantiation
#print axioms support_card
#print axioms support_compl_card
#print axioms boundary_eq_outgoing
#print axioms product_over_sum_ge_half_min
#print axioms boundary_expansion
#print axioms fixedCoefficient_pos
#print axioms actual_family_expansion
#print axioms port_cut_of_spectral
set_option pp.fullNames true in
#check actual_family_expansion
set_option pp.fullNames true in
#check port_cut_of_spectral
example : min (2 : Real) 6 / 2 ≤ 2 * 6 / (2 + 6) := by norm_num
example : min (6 : Real) 2 / 2 ≤ 6 * 2 / (6 + 2) := by norm_num
example : min (0 : Real) 6 / 2 ≤ 0 * 6 / (0 + 6) := by norm_num
example : 0 < fixedCoefficient := fixedCoefficient_pos
