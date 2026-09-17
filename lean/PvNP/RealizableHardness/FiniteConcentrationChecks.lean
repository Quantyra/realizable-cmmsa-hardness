import PvNP.RealizableHardness.FiniteConcentration

namespace PvNP.RealizableHardness.FiniteConcentration
open scoped BigOperators

lemma fair_mean : mean (fun _ : Bool => (1 / 2 : ℚ)) id = 1 / 2 := by
  norm_num [mean, indicator, Bool.forall_bool]

lemma fair_all_true : centeredSum (fun _ : Bool => (1 / 2 : ℚ)) id 2 (fun _ => true) = 1 := by
  unfold centeredSum
  rw [fair_mean]
  norm_num [indicator]

lemma fair_all_false : centeredSum (fun _ : Bool => (1 / 2 : ℚ)) id 2 (fun _ => false) = -1 := by
  unfold centeredSum
  rw [fair_mean]
  norm_num [indicator]

lemma fair_draw_mass (x : Fin 2 → Bool) :
    FiniteSampling.trialMass (fun _ : Bool => (1 / 2 : ℚ)) 2 x = 1 / 4 := by
  norm_num [FiniteSampling.trialMass]

lemma fair_eight_tail :
    probability (fun _ : Bool => (1 / 2 : ℚ)) 8
      (fun x => (1 / 2 : ℝ) ≤ |empirical id 8 x - 1 / 2|) ≤ 2 * Real.exp (-4) := by
  have h := empirical_tail (fun _ : Bool => (1 / 2 : ℚ)) id
    (by intro a; norm_num) (by norm_num) 8 (by omega) (1 / 2) (by norm_num)
  norm_num [fair_mean] at h
  simpa using h

lemma zero_variable_assignment_example :
    probability (fun _ : Bool => (1 / 2 : ℚ)) 8
      (fun x => ∃ _b : Fin 0 → Bool, (1 / 2 : ℝ) ≤ |empirical id 8 x - 1 / 2|) ≤
      2 * Real.exp (-4) := by
  have h := assignment_empirical_tail (fun _ : Bool => (1 / 2 : ℚ)) 0 (fun _ => id)
    (by intro a; norm_num) (by norm_num) 8 (by omega) (1 / 2) (by norm_num)
  norm_num [fair_mean] at h
  simpa using h

#print axioms mean_bounds
#print axioms one_trial_mgf
#print axioms exp_finite_sum
#print axioms product_mgf_identity
#print axioms product_mgf_bound
#print axioms probability_mono
#print axioms exponential_markov
#print axioms upper_tail
#print axioms lower_tail
#print axioms probability_union
#print axioms two_sided_tail
#print axioms probability_exists
#print axioms centered_empirical
#print axioms empirical_tail
#print axioms assignment_empirical_tail
#print axioms assignment_approximation_tail
#print axioms assignment_epsilon_tail
#print axioms probability_complement
#print axioms fair_mean
#print axioms fair_all_true
#print axioms fair_all_false
#print axioms fair_draw_mass
#print axioms fair_eight_tail
#print axioms zero_variable_assignment_example

end PvNP.RealizableHardness.FiniteConcentration