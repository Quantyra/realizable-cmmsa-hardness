/- UNCOMPILED source draft. No author build or independent acceptance claimed. -/
import PvNP.RealizableHardness.SamplerProximity
import PvNP.RealizableHardness.ConditionedCovering

namespace PvNP.RealizableHardness.GoodAdvice
open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence
open PosteriorDensity AdviceExceptions ConditionedCovering SamplerParameters
open DropTailParameters
open PosteriorReweighting (mass)
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact rational cutoff, allowing exact finite conditional probabilities. -/
def zeta (h : ℕ) : ℚ := (1 / 2 : ℚ) ^ (30 * h ^ 2)

lemma zeta_pos (h : ℕ) : 0 < zeta h := by unfold zeta; positivity

lemma zeta_cast (h : ℕ) : (zeta h : ℝ) = decay 30 h := by
  simp [zeta, decay]

/-- The actual low-marginal, posterior-tail and conditional-covering union. -/
def bad (A h : ℕ) (Q : Advice (blocks A h) a) : Bool :=
  exceptional (beta A h) (zeta h) (h ^ 4) Q ||
    badZoom (d := 2 * h) (beta A h) Q

lemma bad_false_iff (A h : ℕ) (Q : Advice (blocks A h) a) :
    bad A h Q = false ↔
      exceptional (beta A h) (zeta h) (h ^ 4) Q = false ∧
      badZoom (d := 2 * h) (beta A h) Q = false := by
  simp [bad]

/-- Union estimate before numerical specialization: all three events are actual. -/
theorem bad_mass_le (A h a : ℕ) (had : a ≤ 2 * h) (hdJ : 2 * h ≤ blocks A h) :
    (mass (ambientMass : Advice (blocks A h) a → ℚ) (bad A h) : ℝ) ≤
      zoomError (beta A h) (blocks A h) +
      3 * (adviceTV (beta A h) (blocks A h) a : ℝ) +
      DropCountTail.tail (beta A h) (blocks A h) (h ^ 4) / decay 30 h := by
  have ha := had.trans hdJ
  have hu := mass_union_le (ambientMass : Advice (blocks A h) a → ℚ)
    (fun Q => (ambientMass_pos Q ha).le)
    (exceptional (beta A h) (zeta h) (h ^ 4)) (badZoom (d := 2 * h) (beta A h))
  have hu' : (mass (ambientMass : Advice (blocks A h) a → ℚ) (bad A h) : ℝ) ≤
      (mass (ambientMass : Advice (blocks A h) a → ℚ)
        (exceptional (beta A h) (zeta h) (h ^ 4)) : ℝ) +
      (mass (ambientMass : Advice (blocks A h) a → ℚ)
        (badZoom (d := 2 * h) (beta A h)) : ℝ) := by
    exact_mod_cast hu
  have he := exceptional_ambient_mass_le_real (beta A h) (beta_nonneg A h)
    (beta_le_one A h) ha (h ^ 4) (zeta h) (zeta_pos h)
  rw [zeta_cast] at he
  have hz := badZoom_mass_le (beta A h) (beta_nonneg A h) (beta_lt_one A h) had hdJ
  linarith

theorem ready_bad_mass_lt {A r h a : ℕ} (hr : SamplerProximity.Ready A r h)
    (ha : a ≤ r) (hah : a ≤ 2 * h)
    (ht : DropCountTail.tail (beta A h) (blocks A h) (h ^ 4) / decay 30 h ≤ decay 70 h) :
    (mass (ambientMass : Advice (blocks A h) a → ℚ) (bad A h) : ℝ) < decay 20 h := by
  have hdim := SamplerProximity.ready_dimensions hr
  have haJ : a ≤ blocks A h := by omega
  have hb := bad_mass_le A h a hah hdim.2
  have hc := CoveringSpan.actual_adviceTV_le_manuscript
    (beta A h) (beta_nonneg A h) (beta_le_one A h) haJ
  change (adviceTV (beta A h) (blocks A h) a : ℝ) ≤ _ at hc
  rw [zoomError_eq_source] at hb
  have hn := SamplerProximity.ready_exceptional hr ha
  linarith

lemma good_marginal_tail (A h : ℕ) (Q : Advice (blocks A h) a)
    (hQ : bad A h Q = false) :
    ambientMass Q / 2 ≤ adviceMarginal (beta A h) Q ∧
      tailMass (beta A h) Q (h ^ 4) ≤ zeta h :=
  good_advice_properties (beta A h) (zeta h) (h ^ 4) Q ((bad_false_iff A h Q).mp hQ).1

lemma good_marginal_pos (A h : ℕ) (Q : Advice (blocks A h) a)
    (haJ : a ≤ blocks A h) (hQ : bad A h Q = false) :
    0 < ambientMass Q / 2 ∧ 0 < adviceMarginal (beta A h) Q := by
  have hp : 0 < ambientMass Q / 2 := div_pos (ambientMass_pos Q haJ) (by norm_num)
  exact ⟨hp, hp.trans_le (good_marginal_tail A h Q hQ).1⟩

theorem ready_good_zoom {A r h a : ℕ} (hr : SamplerProximity.Ready A r h)
    (Q : Advice (blocks A h) a) (hQ : bad A h Q = false) :
    (conditionalDistance (d := 2 * h) (beta A h) Q : ℝ) ≤ decay 100 h := by
  have hz := goodZoom_distance_le (beta A h) Q ((bad_false_iff A h Q).mp hQ).2
  rw [zoomError_eq_source] at hz
  exact hz.trans (SamplerProximity.ready_zoom_scaled hr)

/-- Pointwise posterior density for each actual draw with positive prior mass. -/
theorem good_density (A h : ℕ) (Q : Advice (blocks A h) a)
    (haJ : a + 1 ≤ blocks A h) (hQ : bad A h Q = false)
    (s : Draw (blocks A h)) (hs : dropCount s ≤ h ^ 4) (hp : 0 < prior (beta A h) s) :
    conditional (beta A h) Q s / prior (beta A h) s ≤ 8 * (2 : ℚ) ^ (2 * a * h ^ 4) :=
  conditional_density_le (beta A h) Q s haJ (good_marginal_tail A h Q hQ).1 hs hp

/-- Fixed W may be selected after Q; it is fixed before the conditional draw s.
This bounds each event separately, with no union over W. -/
theorem ready_fixed_rank_failure {A r h a : ℕ} (hr : SamplerProximity.Ready A r h)
    (ha : a ≤ r) (Q : Advice (blocks A h) a) (hQ : bad A h Q = false)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hc : SubspaceRestriction.codim W ≤ r) :
    mass (conditional (beta A h) Q)
      (fun s => decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) ≤
        2 * zeta h := by
  have haJ : a + 1 ≤ blocks A h := by
    have := (SamplerProximity.ready_dimensions hr).1
    omega
  have hg := good_marginal_tail A h Q hQ
  have ht := fixed_subspace_failure_transfer (beta A h) (beta_nonneg A h)
    (beta_le_one A h) Q haJ hg.1 W (h ^ 4)
  have hp : 1 ≤ 2 ^ SubspaceRestriction.codim W := one_le_pow₀ (by norm_num)
  have hcount : (((2 ^ SubspaceRestriction.codim W - 1 : ℕ) : ℚ) : ℝ) =
      (2 : ℝ) ^ SubspaceRestriction.codim W - 1 := by
    rw [Rat.cast_natCast, Nat.cast_sub hp]
    norm_cast
  have ht' : (mass (conditional (beta A h) Q)
      (fun s => decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) : ℝ) ≤
      8 * (2 : ℝ) ^ (2 * a * h ^ 4) *
        (((2 ^ SubspaceRestriction.codim W - 1 : ℕ) : ℚ) : ℝ) * (beta A h : ℝ) +
          (tailMass (beta A h) Q (h ^ 4) : ℝ) := by
    have htcast := (Rat.cast_le (K := ℝ)).mpr ht
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at htcast
    simpa only [mul_assoc] using htcast
  rw [hcount] at ht'
  have hd := SamplerProximity.ready_density hr ha hc
  have htail : (tailMass (beta A h) Q (h ^ 4) : ℝ) ≤ decay 30 h := by
    rw [← zeta_cast]
    exact_mod_cast hg.2
  have hfinal : (mass (conditional (beta A h) Q)
      (fun s => decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) : ℝ) ≤
        2 * (zeta h : ℝ) := by rw [zeta_cast]; linarith
  exact_mod_cast hfinal

/-- All advertised properties refer to the actual samplers and their actual events. -/
def Properties (A r h a : ℕ) (Q : Advice (blocks A h) a) : Prop :=
  0 < ambientMass Q / 2 ∧ ambientMass Q / 2 ≤ adviceMarginal (beta A h) Q ∧
  0 < adviceMarginal (beta A h) Q ∧ tailMass (beta A h) Q (h ^ 4) ≤ zeta h ∧
  (conditionalDistance (d := 2 * h) (beta A h) Q : ℝ) ≤ decay 100 h ∧
  (∑ L : Advice (blocks A h) (2 * h), deletedConditional (beta A h) Q L) = 1 ∧
  (∀ s : Draw (blocks A h), dropCount s ≤ h ^ 4 → 0 < prior (beta A h) s →
    conditional (beta A h) Q s / prior (beta A h) s ≤ 8 * (2 : ℚ) ^ (2 * a * h ^ 4)) ∧
  (∀ W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)),
    Q.val ≤ W → SubspaceRestriction.codim W ≤ r →
    mass (conditional (beta A h) Q)
      (fun s => decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) ≤
        2 * zeta h)

theorem ready_good_properties {A r h a : ℕ} (hr : SamplerProximity.Ready A r h)
    (ha : a ≤ r) (hah : a ≤ 2 * h) (Q : Advice (blocks A h) a)
    (hQ : bad A h Q = false) : Properties A r h a Q := by
  have hd := SamplerProximity.ready_dimensions hr
  have haJ : a + 1 ≤ blocks A h := by omega
  have hp := good_marginal_pos A h Q (by omega) hQ
  have hg := good_marginal_tail A h Q hQ
  exact ⟨hp.1, hg.1, hp.2, hg.2, ready_good_zoom hr Q hQ,
    deletedConditional_normalized (beta A h) (beta_nonneg A h) (beta_lt_one A h) Q hah hd.2,
    fun s hs hspos => good_density A h Q haJ hQ s hs hspos,
    fun W _ hc => ready_fixed_rank_failure hr ha Q hQ W hc⟩

/-- One threshold chosen after fixed A,r proves the full good-advice statement.
There are no supplied closeness, tail, readiness or exceptional-mass hypotheses. -/
theorem eventual_good_advice (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, r < N ∧ ∀ h : ℕ, N ≤ h →
      r < h ∧ 2 * h ≤ blocks A h ∧
      ∀ a : ℕ, a ≤ r → a < 2 * h ∧
        (mass (ambientMass : Advice (blocks A h) a → ℚ) (bad A h) : ℝ) < decay 20 h ∧
        ∀ Q : Advice (blocks A h) a, bad A h Q = false → Properties A r h a Q := by
  obtain ⟨NP, hNP⟩ := SamplerProximity.eventually_ready A r hA
  obtain ⟨NT, hNT⟩ := SamplerParameters.eventual_actual_tail A hA
  refine ⟨max (max NP NT) (r + 1), by omega, ?_⟩
  intro h hh
  have hr := hNP h (show NP ≤ h by omega)
  have ht := (hNT h (show NT ≤ h by omega)).2
  have hlarge : r < h := by omega
  refine ⟨hlarge, (SamplerProximity.ready_dimensions hr).2, ?_⟩
  intro a ha
  have hah : a < 2 * h := by omega
  exact ⟨hah, ready_bad_mass_lt hr ha hah.le ht,
    fun Q hQ => ready_good_properties hr ha hah.le Q hQ⟩

end
end PvNP.RealizableHardness.GoodAdvice
