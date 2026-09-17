import PvNP.RealizableHardness.GoodAdvice

/-! UNCOMPILED: axiom profiles and boundary examples await execution. -/
open PvNP.RealizableHardness
open GoodAdvice SamplerParameters GrassmannIncidence PosteriorDensity
open TripleRestrictionRank TripleRestrictionDimension DropTailParameters
open PosteriorReweighting (mass)
open scoped BigOperators

#print axioms zeta_pos
#print axioms zeta_cast
#print axioms bad_false_iff
#print axioms bad_mass_le
#print axioms ready_bad_mass_lt
#print axioms good_marginal_tail
#print axioms good_marginal_pos
#print axioms ready_good_zoom
#print axioms good_density
#print axioms ready_fixed_rank_failure
#print axioms ready_good_properties
#print axioms eventual_good_advice

noncomputable section
attribute [local instance] Classical.propDecidable

example : zeta 0 = 1 := by simp [zeta]
example (h : ℕ) : 0 < zeta h := zeta_pos h
example (h : ℕ) : (zeta h : ℝ) = decay 30 h := zeta_cast h

-- Zero mean is excluded from the final eventual theorem's A>0 domain.
example (h : ℕ) : beta 0 h = 0 := beta_zero_A h

-- The final threshold is strictly above r, including r=0.
example : ∃ N : ℕ, 0 < N ∧ ∀ h : ℕ, N ≤ h →
    0 < h ∧ 2 * h ≤ blocks 1 h ∧
    ∀ a : ℕ, a ≤ 0 → a < 2 * h ∧
      (mass (ambientMass : Advice (blocks 1 h) a → ℚ) (bad 1 h) : ℝ) < decay 20 h ∧
      ∀ Q : Advice (blocks 1 h) a, bad 1 h Q = false → Properties 1 0 h a Q :=
  eventual_good_advice 1 0 (by decide)

-- Null prior atoms have actual zero posterior mass, not a density quotient claim.
example {A h a : ℕ} (Q : Advice (blocks A h) a) (s : Draw (blocks A h))
    (hs : prior (beta A h) s = 0) : conditional (beta A h) Q s = 0 :=
  conditional_zero_prior (beta A h) Q s hs

-- Every fixed W is bounded separately; the quantified event is the actual rank loss.
example {A r h a : ℕ} (hr : SamplerProximity.Ready A r h) (ha : a ≤ r)
    (Q : Advice (blocks A h) a) (hQ : bad A h Q = false)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hc : SubspaceRestriction.codim W ≤ r) :
    mass (conditional (beta A h) Q)
      (fun s => decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) ≤
        2 * zeta h := ready_fixed_rank_failure hr ha Q hQ W hc

-- Failure to lie in any constituent bad event is extracted from the concrete union.
example {A h a : ℕ} (Q : Advice (blocks A h) a) (hQ : bad A h Q = false) :
    AdviceExceptions.exceptional (beta A h) (zeta h) (h ^ 4) Q = false ∧
      ConditionedCovering.badZoom (d := 2 * h) (beta A h) Q = false :=
  (bad_false_iff A h Q).mp hQ

end
