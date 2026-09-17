import PvNP.RealizableHardness.PosteriorReweighting
namespace PvNP.RealizableHardness.PosteriorReweighting
open scoped BigOperators

-- Degenerate atoms remain in the finite carrier.
example : posterior (fun b : Bool => if b then 1 else 0)
    (fun (_ : Bool) (_ : Unit) => 1) () false = 0 := by
  apply zero_prior
  norm_num

example : marginal (fun _ : Bool => (1 : ℚ) / 2)
    (fun (_ : Bool) (q : Bool) => if q then 1 else 0) false = 0 := by
  simp [marginal]

-- A zero-weight bad atom is allowed; the normalized law is computed.
example : normalizer (fun _ : Bool => (1 : ℚ) / 2)
    (fun b : Bool => if b then 1 else 0) = 1 / 2 := by
  norm_num [normalizer, Fintype.sum_bool]

example : (∑ b : Bool, (1 / 2 : ℚ) * (if b then 1 else 0) /
    normalizer (fun _ : Bool => (1 : ℚ) / 2) (fun b : Bool => if b then 1 else 0)) = 1 := by
  norm_num [normalizer, Fintype.sum_bool]

-- Satisfiable small-error conditions with a zero-weight atom of mass 1/8.
example : let r : Bool → ℚ := fun b => if b then 7 / 8 else 1 / 8
    let w : Bool → ℚ := fun b => if b then 1 else 0
    (1 : ℚ) / 2 ≤ normalizer r w ∧ 0 < normalizer r w ∧
    mass (fun b => r b * w b / normalizer r w) (fun b => !b) ≤ 2 * (1 / 8) / 1 ∧
    (∀ a : Bool → ℚ, (∀ b, 0 ≤ a b ∧ a b ≤ 1) →
      |mean r a - (∑ b, r b * w b * a b) / normalizer r w| ≤ 4 * 0 + 4 * (1 / 8) / 1) := by
  dsimp only
  apply normalized_reweighting (g := fun b => b) (p0 := 1) (eta := 0) (zeta := 1 / 8)
  all_goals norm_num [mass, Fintype.sum_bool]
  all_goals intro b; cases b <;> norm_num

#print axioms marginal_nonneg
#print axioms marginal_normalized
#print axioms posterior_normalized
#print axioms bayes_mass
#print axioms zero_prior
#print axioms bayes_ratio
#print axioms joint_zero_of_marginal_zero
#print axioms total_probability
#print axioms posterior_event_cutoff
#print axioms reweight_error
#print axioms normalizer_deviation
#print axioms normalized_reweighting
#print axioms reweighted_normalized
end PvNP.RealizableHardness.PosteriorReweighting
