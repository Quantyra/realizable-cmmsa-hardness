import PvNP.RealizableHardness.MatrixLiftExactBudgetZoom

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.MatrixLiftExactBudgetZoom
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

#check betweenInsideEquiv
#check card_between
#check refineFlagEquiv
#check sum_refine_flags
#check gaussian_pos_of_le
#check smaller_budget_zoom_density_le
#check homogeneous_lift_density_of_exact_budget
#check ExactBudgetZoomBound
#check smaller_budget_of_exact_r
#check homogeneous_lift_density_of_exact_r

#print axioms card_between
#print axioms sum_refine_flags
#print axioms gaussian_pos_of_le
#print axioms sum_refine_flags_constant
#print axioms refine_flag_card_identity
#print axioms smaller_budget_zoom_density_le
#print axioms homogeneous_lift_density_of_exact_budget
#print axioms smaller_budget_of_exact_r
#print axioms homogeneous_lift_density_of_exact_r

example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (Q W : Submodule (ZMod 2) V) (d : ℕ)
    (h : IsEmpty (Between Q W d)) :
    (∑ L : Between Q W d, (1 : ℝ)) = 0 := by
  letI : IsEmpty (Between Q W d) := h
  simp

end
