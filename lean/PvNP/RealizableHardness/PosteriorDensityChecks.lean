/- UNCOMPILED checks: all examples and axiom queries below are UNRUN. -/
import PvNP.RealizableHardness.PosteriorDensity

namespace PvNP.RealizableHardness.PosteriorDensityChecks
open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence GrassmannCounting
open PosteriorDensity
noncomputable section

#print axioms card_advice
#print axioms ambientMass_eq
#print axioms ambientMass_pos
#print axioms ambientMass_normalized
#print axioms marginal_pos_of_good
#print axioms kernel_div_marginal_le
#print axioms conditional_density_le
#print axioms conditional_zero_prior
#print axioms conditional_mass_le
#print axioms event_transfer
#print axioms fixed_subspace_failure_transfer

-- The ambient law is an actual finite distribution, including empty-coordinate space.
example : (∑ Q : Advice 0 0, ambientMass Q) = 1 := ambientMass_normalized (by omega)
example (Q : Advice J 0) : ambientMass Q = 1 := by
  rw [ambientMass_eq, gaussian_zero]
  norm_num

-- Noncontained advice has exactly zero posterior, for every numerical beta.
example (β : ℚ) (Q : Advice J a) (d : Draw J) (h : ¬ Q.val ≤ retained d) :
    conditional β Q d = 0 := conditional_support β Q d h

-- Zero prior atoms require no division by a positive prior.
example (β : ℚ) (Q : Advice J a) (d : Draw J) (h : prior β d = 0) :
    conditional β Q d = 0 := conditional_zero_prior β Q d h

-- A good marginal cannot be a null conditioning event.
example (β : ℚ) (Q : Advice J a) (ha : a ≤ J)
    (h : adviceMarginal β Q = 0) : ¬ ambientMass Q / 2 ≤ adviceMarginal β Q := by
  intro hg
  have hp := marginal_pos_of_good β Q ha hg
  rw [h] at hp
  exact (lt_irrefl 0) hp

-- With cutoff zero the pointwise mass loss is at most eight.
example (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (Q : Advice J a) (d : Draw J)
    (ha : a + 1 ≤ J) (hg : ambientMass Q / 2 ≤ adviceMarginal β Q)
    (hd : dropCount d = 0) : conditional β Q d ≤ 8 * prior β d := by
  simpa using conditional_mass_le β hβ hβ1 Q d ha hg (T := 0) (by omega)

-- The positive-prior density theorem permits a zero-dimensional advice space.
example (β : ℚ) (Q : Advice J 0) (d : Draw J) (hJ : 1 ≤ J)
    (hg : ambientMass Q / 2 ≤ adviceMarginal β Q) (hd : 0 < prior β d) :
    conditional β Q d / prior β d ≤ 8 := by
  simpa using conditional_density_le β Q d hJ hg (T := dropCount d) le_rfl hd

end
end PvNP.RealizableHardness.PosteriorDensityChecks
