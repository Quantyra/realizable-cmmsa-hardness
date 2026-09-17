/- UNCOMPILED checks, all queries and examples below are unrun. -/
import PvNP.RealizableHardness.GrassmannFlagPosterior
open PvNP.RealizableHardness
#print axioms GrassmannFlagPosterior.quotient_map_dimension
#print axioms GrassmannFlagPosterior.upperQuotientEquiv
#print axioms GrassmannFlagPosterior.card_upper
#print axioms GrassmannFlagPosterior.upperCount_eq
#print axioms GrassmannFlagPosterior.lowerCount
#print axioms GrassmannFlagPosterior.sum_upperCount
#print axioms GrassmannFlagPosterior.flag_product
#print axioms GrassmannFlagPosterior.upperCount_ratio
#print axioms GrassmannFlagPosterior.relativeUpperEquiv
#print axioms GrassmannFlagPosterior.card_relativeUpper
#print axioms GrassmannFlagPosterior.containmentProbability_count
#print axioms GrassmannFlagPosterior.containmentProbability_formula
#print axioms GrassmannFlagPosterior.containmentProbability_noncontainment
#print axioms GrassmannFlagPosterior.eventPosterior_null
#print axioms GrassmannFlagPosterior.eventMarginal_formula
#print axioms GrassmannFlagPosterior.eventPosterior_eq_conditional

example : GrassmannCounting.gaussian 3 0 = 1 :=
  GrassmannCounting.gaussian_zero 3
example : GrassmannCounting.gaussian 3 3 = 1 :=
  GrassmannCounting.gaussian_self 3

example (s : TripleRestrictionRank.Draw J) (Q : GrassmannIncidence.Advice J a)
    (ha : a ≤ J) :
    GrassmannFlagPosterior.containmentProbability s a Q = GrassmannIncidence.kernel s Q := by
  rw [GrassmannFlagPosterior.containmentProbability_formula s a Q le_rfl ha,
    GrassmannCounting.gaussian_self]
  simp

example (β : ℚ) (d : ℕ) (Q : GrassmannIncidence.Advice J a)
    (h : GrassmannFlagPosterior.eventMarginal β d Q = 0) (s : TripleRestrictionRank.Draw J) :
    GrassmannFlagPosterior.eventPosterior β d Q s = 0 :=
  GrassmannFlagPosterior.eventPosterior_null β d Q h s
