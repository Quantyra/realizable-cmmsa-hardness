import PvNP.RealizableHardness.Formula

/-! Scoped axiom audit and nonvacuous finite promise examples. -/
namespace PvNP.RealizableHardness

theorem no_instance_example :
    ∀ x : Unit → Bool, weight (fun _ : Unit => (1 : ℚ)) x ≤ (8 : ℚ) * (1 / 32) →
      average (fun _ : Unit => x ()) < 1 / 4 := by
  intro x hx
  cases h : x ()
  all_goals simp [weight, average, h] at *
  all_goals norm_num at *

theorem yes_instance_example :
    weight (fun _ : Unit => (1 : ℚ)) (fun _ => true) ≤ 1 ∧
    average (fun _ : Unit => true) = 1 := by
  constructor
  · simp [weight]
  · exact average_true

#print axioms exception_completeness
#print axioms exception_soundness
#print axioms repairedWeight_eq_sum
#print axioms repairedWeights_pos
#print axioms repairedWeights_sum
#print axioms repairedBudget_pos
#print axioms repairedBudget_le_one
#print axioms Formula.eval_repair
#print axioms Formula.leaves_repair
#print axioms Formula.repair_complete
#print axioms Formula.repair_sound
#print axioms no_instance_example
#print axioms yes_instance_example
end PvNP.RealizableHardness
