import PvNP.RealizableHardness.MatrixGrassmannIdentity
/-! SOURCE ONLY: profile queries and examples have not been run. -/
open PvNP.RealizableHardness GrassmannCounting MatrixGrassmannMoment MatrixGrassmannIdentity
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

#print axioms rankProbability_bounds
#print axioms rankProbability_positive
#print axioms rankProbability_count
#print axioms array_card
#print axioms rankArray_ratio
#print axioms containing_count
#print axioms containing_card_pos
#print axioms normalized_extension_law
#print axioms rawF_deficient
#print axioms rawTF_frame
#print axioms iid_mean_power
#print axioms grassmannExperiment_eq
#print axioms base_rank_ratio
#print axioms matrix_grassmann_identity
#print axioms product_failure_le
#print axioms rankProbability_loss
#print axioms alpha_bounds
#print axioms alpha_loss_bound
#print axioms alpha_zero_dimension
#print axioms alpha_zero_copies
#print axioms grassmannExperiment_nonneg
#print axioms grassmann_le_twice_moment
#print axioms matrixExperiment_eq
#print axioms above_card_pos
#print axioms grassmannExperiment_all
#print axioms PvNP.RealizableHardness.MatrixGrassmannIdentity.prod_indicator
#print axioms rankEventProbability_eq_experiment
#print axioms rankEventProbability_eq_alpha
#print axioms rankProbability_zero_width
#print axioms alpha_zero_width
#print axioms alpha_zero_base
#print axioms alpha_zero_ambient
#print axioms deficient_integrand
#print axioms rawTF_deficient
#print axioms matrixMoment_zero_copies
#print axioms grassmannExperiment_zero_copies
#print axioms grassmann_le_twice_moment_zero_dimension

example (n d : ℕ) : rankProbability n d 0 = 1 := rankProbability_zero_width n d
example (n t : ℕ) : alpha n 0 0 t = 1 := alpha_zero_dimension n t
example (n d w : ℕ) : alpha n d w 0 = rankProbability n 0 d := alpha_zero_copies n d w
example (n d t : ℕ) : alpha n d 0 t = rankProbability n 0 d := alpha_zero_width n d t
example (n w t : ℕ) : alpha n 0 w t = (rankProbability n 0 w)^t := alpha_zero_base n w t
example {d w t : ℕ} (h : d+w ≤ 0) : alpha 0 d w t = 1 := alpha_zero_ambient h

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
example {d w : ℕ} (h : d+w ≤ Module.finrank (ZMod 2) V) (t : ℕ)
    (Rset : Grass V d → Bool) (Lset : Grass V (d+w) → Bool) :
    matrixExperiment Rset Lset t =
      alpha (Module.finrank (ZMod 2) V) d w t * grassmannExperiment Rset Lset t := by
  rw [matrixExperiment_eq,matrix_grassmann_identity h]

example {d w : ℕ} (h : d+w ≤ Module.finrank (ZMod 2) V) (t : ℕ) :
    rankEventProbability (V := V) d w t = alpha (Module.finrank (ZMod 2) V) d w t :=
  rankEventProbability_eq_alpha h t

example {d w : ℕ} (Rset : Grass V d → Bool) (Lset : Grass V (d+w) → Bool)
    (M : Fin d → V) (hM : ¬LinearIndependent (ZMod 2) M) :
    rawG Rset M * (rawTF Lset M)^0 = 0 := deficient_integrand Rset Lset 0 M hM

example (Rset : Grass V 0 → Bool) (Lset : Grass V (0+0) → Bool) (t : ℕ) :
    grassmannExperiment Rset Lset t ≤ 2*matrixMoment Rset Lset t :=
  grassmann_le_twice_moment_zero_dimension Rset Lset t

example {n d w t : ℕ} (h : d+w ≤ n) (hD : 0 < d+w) :
    1-alpha n d w t ≤ ((d+t*w : ℕ):ℝ)*(2:ℝ)^(d+w-1)/(2:ℝ)^n :=
  alpha_loss_bound h hD

end
