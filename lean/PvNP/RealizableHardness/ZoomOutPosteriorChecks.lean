/- UNCOMPILED checks. No axiom reports or examples have run. -/
import PvNP.RealizableHardness.ZoomOutPosterior
open PvNP.RealizableHardness
open ZoomOutPosterior SamplerParameters GaussianNearOne GrassmannIncidence
open TripleRestrictionRank PosteriorReweighting
open scoped BigOperators

#print axioms qdecay_cast
#print axioms leading_half
#print axioms leading_pos
#print axioms leading_le_one
#print axioms ready_half_dimension
#print axioms eta_le_decay20
#print axioms zeta_div_le_decay20
#print axioms numerical_small
#print axioms retained_conditional_nonneg
#print axioms weight_bounds
#print axioms intersection_finrank
#print axioms stable_dimension
#print axioms bad_mass_eq
#print axioms bounds_relative
#print axioms ready_comparison
#print axioms eventual_comparison
#print axioms conclusion_score_real

example : eta 0 = 1 := by norm_num [eta]
example : eta 5 = 1/4 := by norm_num [eta]
example : qdecay 12 0 = 1 := by norm_num [qdecay]
example (b : ℕ) : leading b 0 = 1 := by simp [leading]
example (h a : ℕ) (hh : 0 < h) :
    GoodAdvice.zeta h / leading (2*h-a) 0 ≤ qdecay 20 h :=
  zeta_div_le_decay20 (r := 0) hh le_rfl

example {J a : ℕ} (β : ℚ) (Q : Advice J a) (s : Draw J)
    (hq : ¬ Q.val ≤ retained s) : conditional β Q s = 0 :=
  conditional_support β Q s hq

example {J a d : ℕ} (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    ZoomOutIncidence.retainedZoomMass s Q W d ≤ 1 := (weight_bounds s Q W).2

example {A r h a : ℕ} (hr : SamplerProximity.Ready A r h) (hh : r < h)
    (hc : 0 ≤ r) :
    4*eta (blocks A h)+8*GoodAdvice.zeta h/leading (2*h-a) 0 < qdecay 12 h :=
  (numerical_small hr hh hc).2

example (r : ℕ) : ∃ N : ℕ, ∀ h : ℕ, N ≤ h → ∀ a : ℕ, a ≤ r →
    ∀ Q : Advice (blocks 1 h) a, GoodAdvice.bad 1 h Q = false →
    ∀ W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks 1 h)),
      Q.val ≤ W → SubspaceRestriction.codim W ≤ r → Conclusion 1 h a Q W :=
  eventual_comparison 1 r (by omega)
