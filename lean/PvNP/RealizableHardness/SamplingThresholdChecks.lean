import PvNP.RealizableHardness.SamplingThreshold

/-! Scoped mathematical sample-size checks; no runtime or probability oracle. -/
namespace PvNP.RealizableHardness.SamplingThreshold

theorem zero_variables_positive_example : 0 < sampleCount 0 1 := sampleCount_pos 0 1

theorem positive_variables_threshold_example : threshold 3 (1 / 2) ≤ sampleCount 3 (1 / 2) :=
  sampleCount_lower 3 (1 / 2)

theorem inverse_error_numeric_example : sampleCount 3 (1 / 2) ≤ 2048 := by
  have h := sampleCount_bound_of_inverse_error 3 2 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem selected_count_failure_example :
    (2 ^ 3 : ℝ) * (2 * Real.exp (-2 * (sampleCount 3 (1 / 2) : ℝ) * ((1 / 2 : ℝ) / 8) ^ 2)) ≤ 1 / 3 :=
  sampleCount_failure_budget 3 (1 / 2) (by norm_num)

theorem explicit_count_failure_example : 4 * Real.exp (-16) ≤ (1 / 3 : ℝ) := by
  have ht : threshold 1 1 ≤ (512 : ℝ) := by
    have h := threshold_numeric_upper 1 1 (by norm_num)
    norm_num at h
    linarith
  have h := failure_budget 1 512 1 (by norm_num) ht
  norm_num at h
  nlinarith

theorem learning_selected_count_failure_example :
    (2 ^ 3 : ℝ) * (2 * Real.exp (-2 * (learningSampleCount 3 (1 / 2) : ℝ) * ((1 / 2 : ℝ) / 8) ^ 2)) ≤ 1 / 6 :=
  learningSampleCount_failure_budget 3 (1 / 2) (by norm_num)

theorem learning_explicit_count_failure_example : 4 * Real.exp (-32) ≤ (1 / 6 : ℝ) := by
  have ht : learningThreshold 1 1 ≤ (1024 : ℝ) := by
    have h := learningThreshold_numeric_upper 1 1 (by norm_num)
    norm_num at h
    linarith
  have h := learning_failure_budget 1 1024 1 (by norm_num) ht
  norm_num at h
  nlinarith

#print axioms threshold_pos
#print axioms threshold_gt_one
#print axioms sampleCount_pos
#print axioms sampleCount_lower
#print axioms sampleCount_least
#print axioms sampleCount_upper
#print axioms failure_budget
#print axioms sampleCount_failure_budget
#print axioms threshold_numeric_upper
#print axioms sampleCount_numeric_upper
#print axioms sampleCount_bound_of_inverse_error
#print axioms failure_budget_of_log_threshold
#print axioms threshold_le_learningThreshold
#print axioms learningSampleCount_pos
#print axioms learningSampleCount_lower
#print axioms learningSampleCount_least
#print axioms learningSampleCount_upper
#print axioms learning_failure_budget
#print axioms learningSampleCount_failure_budget
#print axioms learningThreshold_numeric_upper
#print axioms learningSampleCount_numeric_upper
#print axioms learningSampleCount_bound_of_inverse_error
#print axioms zero_variables_positive_example
#print axioms positive_variables_threshold_example
#print axioms inverse_error_numeric_example
#print axioms selected_count_failure_example
#print axioms explicit_count_failure_example
#print axioms learning_selected_count_failure_example
#print axioms learning_explicit_count_failure_example

end PvNP.RealizableHardness.SamplingThreshold
