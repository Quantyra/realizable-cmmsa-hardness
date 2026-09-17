import PvNP.RealizableHardness.ZoomOutIncidence

/-! UNCOMPILED checks: these axiom queries and examples have not run. -/
open PvNP.RealizableHardness
open ZoomOutIncidence GrassmannIncidence GrassmannCounting GrassmannFlagPosterior
open TripleRestrictionRank ConditionedCovering
open scoped BigOperators

#print axioms relative_indicator_sum
#print axioms retained_event_mass
#print axioms retained_event_pos
#print axioms retainedConditional_uniform
#print axioms retainedZoomMass_null
#print axioms retainedZoomMass_noncontainment
#print axioms retainedZoomMass_dimension_null
#print axioms retainedZoomMass_outside
#print axioms retainedZoomMass_ratio
#print axioms retainedZoomMass_rank_stable
#print axioms retainedZoomMass_top
#print axioms ambientConditional_uniform
#print axioms ambientZoomMass_ratio
#print axioms ambientZoomMass_codimension

noncomputable section
attribute [local instance] Classical.propDecidable

-- Null conditioning remains zero; it is not silently normalized.
example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hz : containmentProbability s d Q = 0) : retainedZoomMass s Q W d = 0 :=
  retainedZoomMass_null s Q W hz

-- Noncontainment is a genuine null fibre.
example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQ : ¬ Q.val ≤ retained s) : retainedZoomMass s Q W d = 0 :=
  retainedZoomMass_noncontainment s Q W hQ

example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hd : Module.finrank (ZMod 2) (retained s) < d) : retainedZoomMass s Q W d = 0 :=
  retainedZoomMass_dimension_null s Q W hd

example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQW : ¬ Q.val ≤ W) : retainedZoomMass s Q W d = 0 :=
  retainedZoomMass_outside s Q W hQW

-- The full-space event has probability one on every valid retained fibre.
example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (hQ : Q.val ≤ retained s) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s)) :
    retainedZoomMass s Q ⊤ d = 1 := retainedZoomMass_top s Q hQ had hd

-- d=a leaves only the advice itself, so every W containing Q has mass one.
example {J a : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ W)
    (ha : a ≤ Module.finrank (ZMod 2) (retained s)) :
    retainedZoomMass s Q W a = 1 := by
  rw [retainedZoomMass_ratio s Q W hQV hQW le_rfl ha]
  simp [gaussian_zero]

-- Insufficient intersection dimension gives a zero numerator, not a positivity premise.
example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQV : Q.val ≤ retained s) (hQW : Q.val ≤ W) (had : a ≤ d)
    (hd : d ≤ Module.finrank (ZMod 2) (retained s))
    (hsmall : Module.finrank (ZMod 2) ↥(retained s ⊓ W) - a < d - a) :
    retainedZoomMass s Q W d = 0 := by
  rw [retainedZoomMass_ratio s Q W hQV hQW had hd, gaussian_of_lt hsmall]
  simp

example {J a : ℕ} (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hQW : Q.val ≤ W) (ha : a ≤ J) : ambientZoomMass Q W a = 1 := by
  rw [ambientZoomMass_ratio Q W hQW le_rfl ha]
  simp [gaussian_zero]

-- Codimension zero and b=0 cause no division singularity.
example : (gaussian (3 - 0 - 0) (0 - 0) : ℚ) / gaussian (3 - 0) (0 - 0) = 1 := by
  norm_num [gaussian_zero]

end
