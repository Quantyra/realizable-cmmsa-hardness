import PvNP.RealizableHardness.SamplingGuarantee

namespace PvNP.RealizableHardness.SamplingGuarantee
open scoped BigOperators
open FiniteSampling JointSamplingLaw FiniteConcentration

def atoms (i : ℕ) : ℚ := if i = 0 then 1 / 3 else if i = 1 then 2 / 3 else 0

lemma atoms_nonneg : ∀ i, 0 ≤ atoms i := by
  intro i
  unfold atoms
  split_ifs <;> norm_num

lemma atoms_normalized : cumulative atoms 3 = 1 := by
  norm_num [cumulative, atoms, Finset.sum_range_succ]

theorem original_mean_example : originalMean atoms 3 (fun i => decide (i = 0)) = 1 / 3 := by
  norm_num [originalMean, eventMass, atoms, Finset.sum_range_succ]

def family (x : Fin 1 → Bool) (i : ℕ) : Bool := x 0 && decide (i = 0)

theorem chosen_base_example :
    let b := precision 3 (1 / 8)
    let M := SamplingThreshold.sampleCount 1 ((1 / 8 : ℚ) : ℝ)
    (2 / 3 : ℝ) ≤ seedProbability M b
      (fun seeds => Good atoms 3 1 M family (1 / 8) (sampleArray atoms 3 b M atoms_normalized seeds)) := by
  exact chosen_good_probability atoms 3 1 family (1 / 8) atoms_normalized atoms_nonneg (by norm_num)

theorem chosen_learning_example :
    let b := precision 3 (1 / 8)
    let M := SamplingThreshold.learningSampleCount 1 ((1 / 8 : ℚ) : ℝ)
    (5 / 6 : ℝ) ≤ seedProbability M b
      (fun seeds => Good atoms 3 1 M family (1 / 8) (sampleArray atoms 3 b M atoms_normalized seeds)) := by
  exact chosen_learning_good_probability atoms 3 1 family (1 / 8) atoms_normalized atoms_nonneg (by norm_num)

theorem explicit_count_example :
    (2 / 3 : ℝ) ≤ seedProbability 16384 8
      (fun seeds => Good atoms 3 1 16384 family (1 / 8)
        (sampleArray atoms 3 8 16384 atoms_normalized seeds)) := by
  apply good_probability_of_threshold atoms 3 8 1 16384 family (1 / 8)
    atoms_normalized atoms_nonneg (by norm_num) (by norm_num)
  have h := SamplingThreshold.threshold_numeric_upper 1 (1 / 8) (by norm_num)
  norm_num at h ⊢
  linarith

theorem zero_variable_example :
    let b := precision 3 (1 / 8)
    let M := SamplingThreshold.sampleCount 0 ((1 / 8 : ℚ) : ℝ)
    (2 / 3 : ℝ) ≤ seedProbability M b
      (fun seeds => Good atoms 3 0 M (fun _ _ => true) (1 / 8)
        (sampleArray atoms 3 b M atoms_normalized seeds)) := by
  exact chosen_good_probability atoms 3 0 (fun _ _ => true) (1 / 8)
    atoms_normalized atoms_nonneg (by norm_num)

#print axioms finiteMean_eq_eventMass
#print axioms roundedLaw_nonneg
#print axioms roundedLaw_sum
#print axioms roundedMean_error
#print axioms seed_failure_bound
#print axioms seed_success_bound
#print axioms good_probability_of_threshold
#print axioms good_probability_of_learningThreshold
#print axioms precision_bound
#print axioms chosen_good_probability
#print axioms chosen_learning_good_probability
#print axioms atoms_nonneg
#print axioms atoms_normalized
#print axioms original_mean_example
#print axioms chosen_base_example
#print axioms chosen_learning_example
#print axioms explicit_count_example
#print axioms zero_variable_example

end PvNP.RealizableHardness.SamplingGuarantee
