import PvNP.RealizableHardness.BernoulliMGF

/-! Scoped exact endpoint/nondegenerate checks and standard-foundation axiom audit. -/
namespace PvNP.RealizableHardness.BernoulliMGF

theorem probability_zero_example (t : ℝ) :
    (1 - (0 : ℝ)) * Real.exp (-t * 0) + 0 * Real.exp (t * (1 - 0)) = 1 := by
  simp

theorem probability_one_example (t : ℝ) :
    (1 - (1 : ℝ)) * Real.exp (-t * 1) + 1 * Real.exp (t * (1 - 1)) = 1 := by
  simp

theorem parameter_zero_example (p : ℝ) :
    (1 - p) * Real.exp (-(0 : ℝ) * p) + p * Real.exp (0 * (1 - p)) =
      Real.exp ((0 : ℝ) ^ 2 / 8) := by
  simp

theorem nondegenerate_example :
    (Real.exp (-1) + Real.exp 1) / 2 ≤ Real.exp (1 / 2) := by
  have h := centered_mgf_le (1 / 2) 2 (by norm_num) (by norm_num)
  norm_num at h
  linarith

theorem negative_parameter_example :
    (Real.exp 1 + Real.exp (-1)) / 2 ≤ Real.exp (1 / 2) := by
  have h := centered_mgf_le (1 / 2) (-2) (by norm_num) (by norm_num)
  norm_num at h
  linarith

#print axioms partition_pos
#print axioms partition_deriv
#print axioms gap_deriv
#print axioms gapSlope_deriv
#print axioms gapCurvature_nonneg
#print axioms gapSlope_monotone
#print axioms gap_nonneg
#print axioms centered_mgf_le
#print axioms probability_zero_example
#print axioms probability_one_example
#print axioms parameter_zero_example
#print axioms nondegenerate_example
#print axioms negative_parameter_example

end PvNP.RealizableHardness.BernoulliMGF
