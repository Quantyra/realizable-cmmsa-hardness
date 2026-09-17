import PvNP.RealizableHardness.WeightRounding

/-! Kernel checks: actual rounding, active clipping, nonempty YES/NO promises, axiom profiles. -/
namespace PvNP.RealizableHardness.WeightRounding

theorem fractional_coordinate_example :
    coordinate (fun b : Bool => if b then (2 / 3 : ℚ) else 1 / 3) 128 false = 43 ∧
    coordinate (fun b : Bool => if b then (2 / 3 : ℚ) else 1 / 3) 128 true = 86 := by
  norm_num [coordinate]
  constructor
  · exact (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  · exact (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)

theorem fractional_denominator_example :
    denominator (fun b : Bool => if b then (2 / 3 : ℚ) else 1 / 3) 128 = 129 ∧
    budgetNumerator (fun b : Bool => if b then (2 / 3 : ℚ) else 1 / 3) 128 (1 / 3) = 45 := by
  have h43 : ⌈(128 / 3 : ℚ)⌉₊ = 43 := (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  have h86 : ⌈(256 / 3 : ℚ)⌉₊ = 86 := (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num [denominator, budgetNumerator, coordinate, Fintype.sum_bool]
  norm_num [h43, h86]

theorem dyadic_scale_example : dyadicScale 1 (1 / 16) = 256 := by
  have hu : Nat.clog 2 256 <= 8 := (Nat.clog_le_iff_le_pow (by decide)).mpr (by decide)
  have hl : 7 < Nat.clog 2 256 := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by decide)
  have hc : Nat.clog 2 256 = 8 := by omega
  norm_num [dyadicScale, hc]

theorem clipped_budget_example :
    denominator (fun _ : Unit => (1 : ℚ)) 16 = 16 ∧
    budgetNumerator (fun _ : Unit => (1 : ℚ)) 16 1 = 16 ∧
    roundedBudget (fun _ : Unit => (1 : ℚ)) 16 1 = 1 := by
  norm_num [denominator, coordinate, budgetNumerator, roundedBudget]

theorem rounded_yes_example :
    weight (roundedWeights (fun _ : Unit => (1 : ℚ)) 16) (fun _ => true) ≤
      roundedBudget (fun _ : Unit => (1 : ℚ)) 16 1 ∧
    average (fun _ : Unit => true) = 1 := by
  constructor
  · norm_num [weight, roundedWeights, roundedBudget, budgetNumerator, denominator, coordinate]
  · exact average_true

theorem rounded_no_example :
    ∀ x : Unit → Bool,
      weight (roundedWeights (fun _ : Unit => (1 : ℚ)) 256) x ≤
        ((5 / 2 : ℕ) : ℚ) * roundedBudget (fun _ : Unit => (1 : ℚ)) 256 (1 / 16) →
      average (fun _ : Unit => x ()) < 1 / 4 := by
  intro x hx
  cases h : x () with
  | false => norm_num [average, h]
  | true =>
    norm_num [weight, roundedWeights, roundedBudget, budgetNumerator, denominator,
      coordinate, h] at hx

#print axioms coordinate_lower
#print axioms coordinate_upper
#print axioms denominator_bounds
#print axioms roundedWeights_pos
#print axioms roundedWeights_sum
#print axioms roundedBudget_valid
#print axioms rounding_complete
#print axioms rounding_budget_transfer
#print axioms rounding_sound
#print axioms dyadicScale_lower
#print axioms dyadicScale_least
#print axioms dyadicScale_upper
#print axioms common_denominator
#print axioms integral_lengths
#print axioms dyadic_denominator_bound
#print axioms denominator_bound_of_inverse_budget
#print axioms polynomial_denominator_bound
#print axioms rounded_lower_bounds
#print axioms formula_rounding
#print axioms fractional_coordinate_example
#print axioms fractional_denominator_example
#print axioms dyadic_scale_example
#print axioms clipped_budget_example
#print axioms rounded_yes_example
#print axioms rounded_no_example

end PvNP.RealizableHardness.WeightRounding
