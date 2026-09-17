/- UNCOMPILED checks. All examples and axiom queries below remain UNRUN. -/
import PvNP.RealizableHardness.AdviceExceptions

namespace PvNP.RealizableHardness.AdviceExceptionsChecks
open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence PosteriorDensity
open AdviceExceptions
open PosteriorReweighting (mass)
noncomputable section
attribute [local instance] Classical.propDecidable

#print axioms tv_nonneg
#print axioms tv_self
#print axioms event_sub_le_tv
#print axioms mass_union_le
#print axioms priorTail_cast
#print axioms conditional_nonneg
#print axioms conditional_zero_marginal
#print axioms tailMass_zero_marginal
#print axioms tailMass_nonneg
#print axioms posterior_tail_expectation
#print axioms null_marginal_not_badTail
#print axioms badTail_marginal_mass_le
#print axioms ambient_event_transfer
#print axioms lowMarginal_ambient_mass_le
#print axioms badTail_ambient_mass_le
#print axioms exceptional_ambient_mass_le
#print axioms good_advice_properties
#print axioms exceptional_ambient_mass_le_real
#print axioms exceptional_chernoff_bound

-- Explicit numerical half-L1 convention, not doubled total variation.
example : tv (fun b : Bool => if b then (1 : ℚ) else 0)
    (fun b : Bool => if b then (0 : ℚ) else 1) = 1 := by
  norm_num [tv, Fintype.sum_bool]

example : tv (fun _ : Bool => (1 / 2 : ℚ)) (fun _ : Bool => (1 / 2 : ℚ)) = 0 :=
  tv_self _

-- Empty event transfer needs no probability-range hypothesis on beta.
example (β : ℚ) (ha : a ≤ J) :
    mass (ambientMass : Advice J a → ℚ) (fun _ => false) ≤
      mass (adviceMarginal β : Advice J a → ℚ) (fun _ => false) + adviceTV β J a :=
  ambient_event_transfer β ha _

-- Null advice has a zero posterior tail, including beta endpoints.
example (Q : Advice J a) (T : ℕ) (hQ : adviceMarginal 1 Q = 0) :
    tailMass 1 Q T = 0 := tailMass_zero_marginal 1 Q T hQ

example (β : ℚ) (Q : Advice J a) (T : ℕ) (hQ : adviceMarginal β Q = 0) :
    badTail β 1 T Q = false := null_marginal_not_badTail β 1 (by norm_num) T Q hQ

-- Empty block space and zero advice dimension are permitted in expectation.
example (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (T : ℕ) :
    (∑ Q : Advice 0 0, adviceMarginal β Q * tailMass β Q T) = priorTail β 0 T :=
  posterior_tail_expectation β hβ hβ1 (by omega) T

-- The beta=0 product law is allowed without any positive prior-atom assumption.
example (ha : a ≤ J) (T : ℕ) :
    mass (adviceMarginal 0 : Advice J a → ℚ) (badTail 0 1 T) ≤ priorTail 0 J T := by
  simpa using badTail_marginal_mass_le 0 (by norm_num) (by norm_num) ha T 1 (by norm_num)

-- Strict tail and low-marginal boundaries leave equality in the good set.
example (β ζ : ℚ) (T : ℕ) (Q : Advice J a) (h : tailMass β Q T = ζ) :
    badTail β ζ T Q = false := by simp [badTail, h]

example (β : ℚ) (Q : Advice J a) (h : adviceMarginal β Q = ambientMass Q / 2) :
    lowMarginal β Q = false := by simp [lowMarginal, h]

-- Final union bound has the exact coefficient three and a single tail loss.
example (ha : a ≤ J) (T : ℕ) :
    mass (ambientMass : Advice J a → ℚ) (exceptional 1 1 T) ≤
      priorTail 1 J T + 3 * adviceTV 1 J a := by
  simpa using exceptional_ambient_mass_le 1 (by norm_num) (by norm_num) ha T 1 (by norm_num)

end
end PvNP.RealizableHardness.AdviceExceptionsChecks
