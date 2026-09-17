import PvNP.RealizableHardness.EqualityGadget

namespace PvNP.RealizableHardness.EqualityGadgetChecks
open EqualityGadget

#print axioms rows_length
#print axioms rows_nodup
#print axioms row_injective
#print axioms support_card
#print axioms support_injective
#print axioms pair_intersection
#print axioms degree_exact
#print axioms extension_terminals
#print axioms violations_lower
#print axioms extension_violations
#print axioms exact_minimum
#print axioms all_satisfied_implies_equal
#print axioms satisfiable_iff_equal
#print axioms relabeledSupport_eq
#print axioms relabeled_row_injective
#print axioms relabeled_support_card
#print axioms relabeled_support_injective
#print axioms relabeled_pair_intersection
#print axioms relabeled_degree
#print axioms relabeled_degree_outside
#print axioms relabeled_satisfied
#print axioms relabeled_violations_lower

#check exact_minimum
#check relabeled_violations_lower

example : violations (extension 0 0) = 0 := by decide
example : violations (extension 1 1) = 0 := by decide
example : violations (extension 0 1) = 1 := by decide
example : violations (extension 1 0) = 1 := by decide
example : degree 0 = 1 ∧ degree 1 = 1 := by decide
example : degree 2 = 2 ∧ degree 3 = 2 ∧ degree 4 = 2 ∧ degree 5 = 2 ∧ degree 6 = 2 := by decide
example : (support 0 ∩ support 1).card = 0 := by decide
example : (support 0 ∩ support 2).card = 1 := by decide
/-- Equal terminals do not force a badly chosen internal assignment to satisfy the gadget. -/
example : violations (![0, 0, 1, 0, 0, 0, 0] : Assignment) = 2 := by decide

example {V : Type*} [DecidableEq V] (f : Var ↪ V) (s : V → ZMod 2) :
    mismatch (s (f 0)) (s (f 1)) ≤ violations (s ∘ f) := violations_lower (s ∘ f)

end PvNP.RealizableHardness.EqualityGadgetChecks
