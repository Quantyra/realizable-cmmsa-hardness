import PvNP.RealizableHardness.ConditionedCovering

/-! UNCOMPILED checks: all axiom reports and examples below remain unrun. -/
open PvNP.RealizableHardness
open ConditionedCovering GrassmannIncidence PosteriorDensity PosteriorReweighting
open scoped BigOperators

#print axioms fibre_conditional_tv_le
#print axioms conditional_tv_average_le
#print axioms flagKernel_nonneg
#print axioms flagKernel_normalized
#print axioms ambient_flag_marginal
#print axioms retained_flag_marginal
#print axioms deleted_flag_marginal
#print axioms adviceMarginal_pos
#print axioms ambientConditional_normalized
#print axioms deletedConditional_normalized
#print axioms ambientConditional_formula
#print axioms deletedConditional_formula
#print axioms retainedConditional_normalized
#print axioms contained_kernel_zero
#print axioms deletedConditional_eq_eventPosterior_mixture
#print axioms deletedConditional_eq_advicePosterior_mixture
#print axioms conditionalDistance_nonneg
#print axioms actual_conditional_average_le
#print axioms zoomError_nonneg
#print axioms zoomError_sq
#print axioms zoomError_eq_source
#print axioms actual_conditional_average_le_real
#print axioms badZoom_mass_le
#print axioms goodZoom_distance_le
#print axioms beta_lt_one_of_source
#print axioms actual_conditioned_covering

example : zoomError 0 1 = 0 := by simp [zoomError]
example : zoomError (1/4) 0 = 0 := by simp [zoomError]
example : zoomError (1/4) 1 ^ 2 = 1/4 := by
  rw [zoomError_sq _ (by norm_num)]
  norm_num
example :
    (mass (ambientMass : Advice 1 0 → ℚ) (badZoom (d := 1) 0) : ℝ) ≤ 0 := by
  simpa [zoomError] using badZoom_mass_le (J := 1) (a := 0) (d := 1)
    0 (by norm_num) (by norm_num) (by omega) (by omega)
example (Q : Advice 1 0) : ∑ L : Advice 1 1, ambientConditional Q L = 1 :=
  ambientConditional_normalized Q (by omega) (by omega)
example (Q : Advice 1 0) : ∑ L : Advice 1 1, deletedConditional (1/16) Q L = 1 :=
  deletedConditional_normalized _ (by norm_num) (by norm_num) Q (by omega) (by omega)
example (Q : Advice 1 0) (L : Advice 1 1) :
    deletedConditional 0 Q L = ∑ s : TripleRestrictionRank.Draw 1,
      conditional 0 Q s * retainedConditional s Q L :=
  deletedConditional_eq_advicePosterior_mixture 0 (by norm_num) (by norm_num)
    Q L (by omega) (by omega)
example : (1/16 : ℚ) < 1 :=
  beta_lt_one_of_source _ (by norm_num) 1 (by norm_num)
example :
    (mass (ambientMass : Advice 1 0 → ℚ) (badZoom (d := 1) (1/16)) : ℝ) ≤
      Real.sqrt ((1/16 : ℚ) : ℝ) * (1 : ℝ)^(1/4 : ℝ) := by
  simpa only [Nat.cast_one] using
    (actual_conditioned_covering (J := 1) (a := 0) (d := 1)
      (1/16) (by norm_num) (by omega) (by omega) (by norm_num)).1
example (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1) (Q : Advice 0 0) :
    (conditionalDistance (d := 0) β Q : ℝ) ≤ zoomError β 0 * (2 : ℝ)^5 := by
  have h := actual_conditional_average_le_real (J := 0) (a := 0) (d := 0)
    β hβ hβ1 (by omega) (by omega)
  have hn : (0 : ℝ) ≤ conditionalDistance (d := 0) β Q := by
    exact_mod_cast conditionalDistance_nonneg (d := 0) β Q
  have hw : (0 : ℝ) < ambientMass Q := by
    exact_mod_cast ambientMass_pos Q (by omega)
  have hs : (ambientMass Q : ℝ) * (conditionalDistance (d := 0) β Q : ℝ) ≤
      ∑ R : Advice 0 0, (ambientMass R : ℝ) * (conditionalDistance (d := 0) β R : ℝ) := by
    apply Finset.single_le_sum (f := fun R : Advice 0 0 =>
      (ambientMass R : ℝ) * (conditionalDistance (d := 0) β R : ℝ))
    · intro R _
      have hp : (0 : ℝ) ≤ ambientMass R := by
        exact_mod_cast (ambientMass_pos R (by omega)).le
      have hd : (0 : ℝ) ≤ conditionalDistance (d := 0) β R := by
        exact_mod_cast conditionalDistance_nonneg (d := 0) β R
      exact mul_nonneg hp hd
    · exact Finset.mem_univ Q
  simp [zoomError] at h
  have hr : (conditionalDistance (d := 0) β Q : ℝ) ≤ 0 := by nlinarith
  simpa [zoomError] using hr
