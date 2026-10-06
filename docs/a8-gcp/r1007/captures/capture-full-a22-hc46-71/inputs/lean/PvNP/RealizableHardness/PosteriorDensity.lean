/- UNCOMPILED source draft. No kernel verification or independent acceptance claimed. -/
import PvNP.RealizableHardness.GaussianRatio

/-! Actual advice posterior density, derived from finite subspace counts.
The cutoff tail remains explicit. No conditional independence or full hardness theorem. -/
namespace PvNP.RealizableHardness.PosteriorDensity
open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence GrassmannCounting
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The uniform law on the actual ambient advice space, not an assumed likelihood. -/
def ambientMass (Q : Advice J a) : ℚ := (Fintype.card (Advice J a) : ℚ)⁻¹

lemma card_advice (J a : ℕ) : Fintype.card (Advice J a) = gaussian (3 * J) a := by
  have h : Nat.card (Advice J a) = gaussian (3 * J) a := by
    change Nat.card (Grass (Vector J) a) = _
    rw [Nat.card_eq_fintype_card, card_grass]
    simp [TripleRestrictionRank.Vector, Coord, Module.finrank_pi, Nat.mul_comm]
  simpa only [Nat.card_eq_fintype_card] using h

lemma ambientMass_eq (Q : Advice J a) :
    ambientMass Q = (gaussian (3 * J) a : ℚ)⁻¹ := by
  rw [ambientMass, card_advice]

lemma ambientMass_pos (Q : Advice J a) (ha : a ≤ J) : 0 < ambientMass Q := by
  rw [ambientMass_eq]
  apply inv_pos.mpr
  exact_mod_cast GaussianRatio.gaussian_pos (show a ≤ 3 * J by omega)

lemma ambientMass_normalized (ha : a ≤ J) : ∑ Q : Advice J a, ambientMass Q = 1 := by
  have hc : (Fintype.card (Advice J a) : ℚ) ≠ 0 := by
    rw [card_advice]
    exact_mod_cast (Nat.ne_of_gt (GaussianRatio.gaussian_pos (show a ≤ 3 * J by omega)))
  simp only [ambientMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hc

/-- The good-marginal condition implies a genuine positive conditioning event. -/
lemma marginal_pos_of_good (β : ℚ) (Q : Advice J a) (ha : a ≤ J)
    (hgood : ambientMass Q / 2 ≤ adviceMarginal β Q) : 0 < adviceMarginal β Q := by
  have hp := ambientMass_pos Q ha
  linarith

/-- Bayes kernel divided by the actual marginal, bounded through the actual two counts. -/
lemma kernel_div_marginal_le (β : ℚ) (Q : Advice J a) (d : Draw J)
    (ha : a ≤ J) (hgood : ambientMass Q / 2 ≤ adviceMarginal β Q) :
    kernel d Q / adviceMarginal β Q ≤
      2 * ((gaussian (3 * J) a : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained d)) a) := by
  have hN : (0 : ℚ) < gaussian (3 * J) a := by
    exact_mod_cast GaussianRatio.gaussian_pos (show a ≤ 3 * J by omega)
  have hC : (0 : ℚ) < gaussian (Module.finrank (ZMod 2) (retained d)) a := by
    rw [← incidenceCount_eq]
    exact_mod_cast incidenceCount_pos d ha
  have hM := marginal_pos_of_good β Q ha hgood
  by_cases hinc : Q.val ≤ retained d
  · rw [kernel, if_pos hinc, incidenceCount_eq]
    apply (div_le_iff₀ hM).mpr
    have hm := mul_le_mul_of_nonneg_left hgood
      (show 0 ≤ 2 * ((gaussian (3 * J) a : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained d)) a) by positivity)
    have hid : (2 * ((gaussian (3 * J) a : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained d)) a)) *
        (ambientMass Q / 2) =
        (gaussian (Module.finrank (ZMod 2) (retained d)) a : ℚ)⁻¹ := by
      rw [ambientMass_eq]
      field_simp [ne_of_gt hN, ne_of_gt hC]
      <;> ring
    rw [hid] at hm
    exact hm
  · rw [kernel, if_neg hinc, zero_div]
    positivity

/-- The requested actual posterior/prior likelihood bound, for a positive prior atom.
No density or Gaussian-ratio inequality occurs among the hypotheses. -/
theorem conditional_density_le (β : ℚ) (Q : Advice J a) (d : Draw J)
    (ha : a + 1 ≤ J) (hgood : ambientMass Q / 2 ≤ adviceMarginal β Q)
    (hT : dropCount d ≤ T) (hd : 0 < prior β d) :
    conditional β Q d / prior β d ≤ 8 * (2 : ℚ)^(2 * a * T) := by
  rw [conditional_ratio β Q d hd]
  apply (kernel_div_marginal_le β Q d (by omega) hgood).trans
  apply GaussianRatio.retained_gaussian_twice_le_cutoff d _ hT
  have hl := retained_finrank_lower d
  rw [retained_finrank_eq] at hl
  omega

lemma conditional_zero_prior (β : ℚ) (Q : Advice J a) (d : Draw J)
    (hd : prior β d = 0) : conditional β Q d = 0 :=
  PosteriorReweighting.zero_prior (prior β) kernel Q d hd

/-- Pointwise domination also covers zero prior atoms, needed for summing events. -/
theorem conditional_mass_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (Q : Advice J a) (d : Draw J) (ha : a + 1 ≤ J)
    (hgood : ambientMass Q / 2 ≤ adviceMarginal β Q) (hT : dropCount d ≤ T) :
    conditional β Q d ≤ (8 * (2 : ℚ)^(2 * a * T)) * prior β d := by
  have hd0 : 0 ≤ prior β d := drawMass_nonneg β hβ hβ1 d
  by_cases hd : prior β d = 0
  · rw [conditional_zero_prior β Q d hd, hd, mul_zero]
  · have hdpos : 0 < prior β d := lt_of_le_of_ne hd0 (Ne.symm hd)
    exact (div_le_iff₀ hdpos).mp (conditional_density_le β Q d ha hgood hT hdpos)

/-- Conditional tail mass is recorded, not silently assumed small. -/
def tailMass (β : ℚ) (Q : Advice J a) (T : ℕ) : ℚ :=
  PosteriorReweighting.mass (conditional β Q) (fun d => decide (T < dropCount d))

theorem event_transfer (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (Q : Advice J a) (ha : a + 1 ≤ J)
    (hgood : ambientMass Q / 2 ≤ adviceMarginal β Q) (b : Draw J → Bool) (T : ℕ) :
    PosteriorReweighting.mass (conditional β Q) b ≤
      (8 * (2 : ℚ)^(2 * a * T)) * PosteriorReweighting.mass (prior β) b + tailMass β Q T := by
  have h := PosteriorReweighting.posterior_event_cutoff (prior β) kernel
    (drawMass_nonneg β hβ hβ1) kernel_nonneg Q b
    (fun d => decide (dropCount d ≤ T)) (8 * (2 : ℚ)^(2 * a * T)) (by positivity)
    (fun d hd => conditional_mass_le β hβ hβ1 Q d ha hgood (of_decide_eq_true hd))
  have he : (fun d : Draw J => !(decide (dropCount d ≤ T))) =
      (fun d : Draw J => decide (T < dropCount d)) := by
    funext d
    by_cases hd : dropCount d ≤ T
    · simp [hd, Nat.not_lt.mpr hd]
    · simp [hd, Nat.lt_of_not_ge hd]
  rw [he] at h
  exact h

set_option maxHeartbeats 800000 in
/-- A fixed W may depend on the already chosen Q, but not on the subsequently sampled d.
The unconditional rank bound is transported without asserting posterior independence. -/
theorem fixed_subspace_failure_transfer (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (Q : Advice J a) (ha : a + 1 ≤ J)
    (hgood : ambientMass Q / 2 ≤ adviceMarginal β Q)
    (W : Submodule (ZMod 2) (Vector J)) (T : ℕ) :
    PosteriorReweighting.mass (conditional β Q)
      (fun d => decide (SubspaceRestriction.codimInRetained W d ≠ SubspaceRestriction.codim W)) ≤
      (8 * (2 : ℚ)^(2 * a * T)) *
        (((2 ^ SubspaceRestriction.codim W - 1 : ℕ) : ℚ) * β) + tailMass β Q T := by
  have hu := SubspaceRestriction.arbitrary_subspace_failure_probability β hβ hβ1 W
  have hu' : PosteriorReweighting.mass (prior β)
      (fun d => decide (SubspaceRestriction.codimInRetained W d ≠ SubspaceRestriction.codim W)) ≤
        ((2 ^ SubspaceRestriction.codim W - 1 : ℕ) : ℚ) * β := by
    convert hu using 1
    unfold PosteriorReweighting.mass probability prior
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : SubspaceRestriction.codimInRetained W d = SubspaceRestriction.codim W
    · simp [hd]
    · simp [hd]
  exact (event_transfer β hβ hβ1 Q ha hgood _ T).trans
    (add_le_add (mul_le_mul_of_nonneg_left hu'
      (by positivity : 0 ≤ (8 * (2 : ℚ)^(2 * a * T)))) le_rfl)

end
end PvNP.RealizableHardness.PosteriorDensity
