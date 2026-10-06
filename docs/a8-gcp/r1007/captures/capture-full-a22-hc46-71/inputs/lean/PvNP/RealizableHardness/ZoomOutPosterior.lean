/- UNCOMPILED source draft; no kernel acceptance is claimed. -/
import PvNP.RealizableHardness.GoodAdvice
import PvNP.RealizableHardness.ZoomOutParameters

namespace PvNP.RealizableHardness.ZoomOutPosterior
open scoped BigOperators
open TripleRestrictionRank GrassmannIncidence GrassmannFlagPosterior ConditionedCovering
open ZoomOutIncidence ZoomOutParameters GaussianNearOne SamplerParameters
open PosteriorReweighting
noncomputable section
attribute [local instance] Classical.propDecidable

def qdecay (k h : ℕ) : ℚ := (1/2 : ℚ)^(k*h^2)
def eta (J : ℕ) : ℚ := 1/(2 : ℚ)^(J/2)

lemma qdecay_cast (k h : ℕ) : (qdecay k h : ℝ) = DropTailParameters.decay k h := by
  simp [qdecay, DropTailParameters.decay]

lemma leading_half (b c : ℕ) : leading b c = (1/2 : ℚ)^(b*c) := by
  simp [leading, one_div, inv_pow]

lemma leading_pos (b c : ℕ) : 0 < leading b c := by unfold leading; positivity
lemma leading_le_one (b c : ℕ) : leading b c ≤ 1 := by
  rw [leading_half]
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma ready_half_dimension {A r h : ℕ} (hr : SamplerProximity.Ready A r h) :
    20*h^2 ≤ blocks A h / 2 := by
  have hE : SamplerProximity.exponent A h ≤ (blocks A h : ℝ) := by
    have hn : 2^(A*h^2) ≤ blocks A h := Nat.le_of_lt Nat.lt_two_pow_self
    unfold SamplerProximity.exponent
    exact_mod_cast hn
  have hm : 0 ≤ SamplerProximity.mean A h := by unfold SamplerProximity.mean; positivity
  have hp : 0 ≤ 2*(r : ℝ)*(h : ℝ)^4 := by positivity
  have hq : 0 ≤ (r : ℝ)*(h : ℝ)^2 := by positivity
  have hb : (40 : ℝ)*(h : ℝ)^2 ≤ (blocks A h : ℝ) := by nlinarith [hr.2]
  have hn : 40*h^2 ≤ blocks A h := by exact_mod_cast hb
  omega

lemma eta_le_decay20 {J h : ℕ} (hh : 20*h^2 ≤ J/2) : eta J ≤ qdecay 20 h := by
  have he : eta J = (1/2 : ℚ)^(J/2) := by simp [eta, one_div, inv_pow]
  rw [he, qdecay]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hh

lemma zeta_div_le_decay20 {r h a c : ℕ} (hh : r < h) (hc : c ≤ r) :
    GoodAdvice.zeta h / leading (2*h-a) c ≤ qdecay 20 h := by
  have hb : (2*h-a)*c ≤ 10*h^2 := by
    have hmul := Nat.mul_le_mul (Nat.sub_le (2*h) a) (show c ≤ h by omega)
    nlinarith
  apply (div_le_iff₀ (leading_pos _ _)).mpr
  rw [leading_half]
  change (1/2 : ℚ)^(30*h^2) ≤ (1/2 : ℚ)^(20*h^2) * (1/2 : ℚ)^((2*h-a)*c)
  rw [← pow_add]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma numerical_small {A r h a c : ℕ} (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (hc : c ≤ r) :
    eta (blocks A h) + (2*GoodAdvice.zeta h)/leading (2*h-a) c ≤ 1/2 ∧
    4*eta (blocks A h) + 8*GoodAdvice.zeta h/leading (2*h-a) c < qdecay 12 h := by
  have he := eta_le_decay20 (ready_half_dimension hr)
  have hz := zeta_div_le_decay20 (a := a) hh hc
  have hh1 : 1 ≤ h := by omega
  have hsq : 1 ≤ h^2 := one_le_pow₀ hh1
  have hd : qdecay 20 h ≤ (1/2 : ℚ)^3 := by
    unfold qdecay
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hd8 : qdecay 8 h ≤ (1/2 : ℚ)^4 := by
    unfold qdecay
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hid : qdecay 20 h = qdecay 12 h * qdecay 8 h := by
    unfold qdecay
    rw [← pow_add]
    congr 1 <;> omega
  have hp : 0 < qdecay 12 h := by unfold qdecay; positivity
  have hstrict : 12*qdecay 20 h < qdecay 12 h := by
    rw [hid]
    norm_num at hd8
    nlinarith
  constructor
  · norm_num at hd
    have hi : (2*GoodAdvice.zeta h)/leading (2*h-a) c =
        2*(GoodAdvice.zeta h/leading (2*h-a) c) := by ring
    rw [hi]
    linarith
  · have hi : 8*GoodAdvice.zeta h/leading (2*h-a) c =
        8*(GoodAdvice.zeta h/leading (2*h-a) c) := by ring
    rw [hi]
    linarith

variable {J a d : ℕ}

lemma retained_conditional_nonneg (s : Draw J) (Q : Advice J a) (L : Advice J d) :
    0 ≤ retainedConditional s Q L := by
  have hn : 0 ≤ containmentProbability s d Q := by
    unfold GrassmannFlagPosterior.containmentProbability
    apply Finset.sum_nonneg
    intro R _
    split_ifs <;> first | exact kernel_nonneg _ _ | exact le_rfl
  unfold retainedConditional
  apply div_nonneg _ hn
  split_ifs <;> first | exact kernel_nonneg _ _ | exact le_rfl

lemma weight_bounds (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    0 ≤ retainedZoomMass s Q W d ∧ retainedZoomMass s Q W d ≤ 1 := by
  have hn : 0 ≤ retainedZoomMass s Q W d := by
    unfold retainedZoomMass
    apply Finset.sum_nonneg
    intro L _
    split_ifs <;> first | exact retained_conditional_nonneg _ _ _ | exact le_rfl
  refine ⟨hn, ?_⟩
  by_cases hz : GrassmannFlagPosterior.containmentProbability s d Q = 0
  · rw [retainedZoomMass_null s Q W hz]
    norm_num
  · have hp : 0 < GrassmannFlagPosterior.containmentProbability s d Q := by
      have hn' : 0 ≤ GrassmannFlagPosterior.containmentProbability s d Q := by
        unfold GrassmannFlagPosterior.containmentProbability
        apply Finset.sum_nonneg
        intro L _
        split_ifs <;> first | exact kernel_nonneg _ _ | exact le_rfl
      exact lt_of_le_of_ne hn' (Ne.symm hz)
    calc
      _ ≤ ∑ L : Advice J d, retainedConditional s Q L := by
        apply Finset.sum_le_sum
        intro L _
        split_ifs <;> first | exact le_rfl | exact retained_conditional_nonneg _ _ _
      _ = 1 := retainedConditional_normalized s Q hp

lemma intersection_finrank (s : Draw J)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    Module.finrank (ZMod 2) (W.comap (retained s).subtype) =
      Module.finrank (ZMod 2) ↥(retained s ⊓ W) := by
  let e : ↥(W.comap (retained s).subtype) ≃ₗ[ZMod 2] ↥(retained s ⊓ W) :=
    { toFun := fun x => ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro k x; rfl }
  exact e.finrank_eq

lemma stable_dimension (s : Draw J)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (hs : SubspaceRestriction.codimInRetained W s = SubspaceRestriction.codim W) :
    Module.finrank (ZMod 2) ↥(retained s ⊓ W) + SubspaceRestriction.codim W =
      Module.finrank (ZMod 2) (retained s) := by
  have hle := (W.comap (retained s).subtype).finrank_le
  unfold SubspaceRestriction.codimInRetained at hs
  rw [intersection_finrank s W] at hs hle
  omega

def goodDraw (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (s : Draw J) : Bool :=
  decide (Q.val ≤ retained s ∧
    SubspaceRestriction.codimInRetained W s = SubspaceRestriction.codim W)

lemma bad_mass_eq (β : ℚ) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    mass (conditional β Q) (fun s => !(goodDraw Q W s)) =
      mass (conditional β Q) (fun s => decide
        (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) := by
  unfold mass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hq : Q.val ≤ retained s
  · by_cases hs : SubspaceRestriction.codimInRetained W s = SubspaceRestriction.codim W
    · simp [goodDraw, hq, hs]
    · simp [goodDraw, hq, hs]
  · simp [goodDraw, hq, conditional_support β Q s hq]

lemma bounds_relative {J n b c : ℕ} {p : ℚ} (hb : Bounds J n b c p) :
    |p/leading b c - 1| ≤ eta J := by
  have hp := leading_pos b c
  apply abs_le.mpr
  constructor
  · have hlo := hb.2.2.2.1
    change leading b c * (1-eta J) ≤ p at hlo
    have hl : 1-eta J ≤ p/leading b c := by
      apply (le_div_iff₀ hp).mpr
      nlinarith [hlo]
    linarith
  · have hu := (div_le_one hp).mpr hb.2.2.1
    have he : 0 ≤ eta J := by unfold eta; positivity
    linarith

/-- Actual normalized posterior after additionally weighting each deletion draw
by its conditional zoom-out event probability. -/
def reweighted (A h : ℕ) (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (s : Draw (blocks A h)) : ℚ :=
  conditional (beta A h) Q s * retainedZoomMass s Q W (2*h) /
    normalizer (conditional (beta A h) Q) (fun t => retainedZoomMass t Q W (2*h))

def Conclusion (A h a : ℕ) (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h))) : Prop :=
  let p0 := leading (2*h-a) (SubspaceRestriction.codim W)
  let Z := normalizer (conditional (beta A h) Q) (fun s => retainedZoomMass s Q W (2*h))
  p0/2 ≤ Z ∧ 0 < Z ∧ (∑ s, reweighted A h Q W s) = 1 ∧
  mass (reweighted A h Q W) (fun s => !(goodDraw Q W s)) ≤ 4*GoodAdvice.zeta h/p0 ∧
  (∀ f : Draw (blocks A h) → ℚ, (∀ s, 0 ≤ f s ∧ f s ≤ 1) →
    |mean (conditional (beta A h) Q) f - mean (reweighted A h Q W) f| ≤
      4*eta (blocks A h)+8*GoodAdvice.zeta h/p0) ∧
  4*eta (blocks A h)+8*GoodAdvice.zeta h/p0 < qdecay 12 h

theorem ready_comparison {A r h a : ℕ} (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (ha : a ≤ r) (Q : Advice (blocks A h) a)
    (hprops : GoodAdvice.Properties A r h a Q)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hQW : Q.val ≤ W) (hc : SubspaceRestriction.codim W ≤ r) : Conclusion A h a Q W := by
  have hpQ := hprops.2.2.1
  have hr0 (s : Draw (blocks A h)) : 0 ≤ conditional (beta A h) Q s := by
    rw [conditional_formula]
    apply div_nonneg _ hpQ.le
    apply mul_nonneg (drawMass_nonneg _ (beta_nonneg A h) (beta_le_one A h) s)
    split_ifs <;> positivity
  have hrn := conditional_normalized (beta A h) Q hpQ
  have hg (s : Draw (blocks A h)) (hs : goodDraw Q W s = true) :
      |retainedZoomMass s Q W (2*h) / leading (2*h-a) (SubspaceRestriction.codim W)-1| ≤
        eta (blocks A h) := by
    have hs' : Q.val ≤ retained s ∧
        SubspaceRestriction.codimInRetained W s = SubspaceRestriction.codim W := by
      simpa [goodDraw] using hs
    exact bounds_relative (retained_bounds hh (ready_budget hr) ha hc s Q W
      hs'.1 hQW (stable_dimension s W hs'.2))
  have hb : mass (conditional (beta A h) Q) (fun s => !(goodDraw Q W s)) ≤
      2*GoodAdvice.zeta h := by
    rw [bad_mass_eq]
    exact hprops.2.2.2.2.2.2.2 W hQW hc
  have hn := numerical_small (a := a) hr hh hc
  have hm := normalized_reweighting (conditional (beta A h) Q)
    (fun s => retainedZoomMass s Q W (2*h)) (goodDraw Q W)
    (leading (2*h-a) (SubspaceRestriction.codim W)) (eta (blocks A h))
    (2*GoodAdvice.zeta h) hr0 hrn (fun s => weight_bounds s Q W)
    (leading_pos _ _) (leading_le_one _ _) (by unfold eta; positivity)
    (by have := GoodAdvice.zeta_pos h; positivity) hn.1 hg hb
  refine ⟨hm.1, hm.2.1, ?_, ?_, ?_, hn.2⟩
  · exact reweighted_normalized _ _ hm.2.1
  · have hfour : (2 : ℚ)*(2*GoodAdvice.zeta h) = 4*GoodAdvice.zeta h := by ring
    change mass (reweighted A h Q W) (fun s => !(goodDraw Q W s)) ≤ _
    unfold reweighted
    simpa only [hfour] using hm.2.2.1
  · intro f hf
    have hmean : mean (reweighted A h Q W) f =
        (∑ s, conditional (beta A h) Q s * retainedZoomMass s Q W (2*h) * f s) /
          normalizer (conditional (beta A h) Q) (fun s => retainedZoomMass s Q W (2*h)) := by
      unfold mean reweighted
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hmean]
    convert hm.2.2.2 f hf using 1 <;> ring

/-- No assumed mass, closeness, readiness or growth remains in this family theorem.
W is fixed after Q and before the conditional deletion draw. -/
theorem eventual_comparison (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → ∀ a : ℕ, a ≤ r →
      ∀ Q : Advice (blocks A h) a, GoodAdvice.bad A h Q = false →
      ∀ W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)),
        Q.val ≤ W → SubspaceRestriction.codim W ≤ r → Conclusion A h a Q W := by
  obtain ⟨NG, hNG, hg⟩ := GoodAdvice.eventual_good_advice A r hA
  obtain ⟨NP, hp⟩ := SamplerProximity.eventually_ready A r hA
  refine ⟨max NG NP, ?_⟩
  intro h hh a ha Q hQ W hQW hc
  have hgood := hg h (show NG ≤ h by omega)
  exact ready_comparison (hp h (by omega)) hgood.1 ha Q
    ((hgood.2.2 a ha).2.2 Q hQ) W hQW hc

theorem conclusion_score_real {A h a : ℕ} (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hC : Conclusion A h a Q W) (f : Draw (blocks A h) → ℚ)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    ((|mean (conditional (beta A h) Q) f - mean (reweighted A h Q W) f| : ℚ) : ℝ) <
      DropTailParameters.decay 12 h := by
  have hb := hC.2.2.2.2.1 f hf
  have hs := hb.trans_lt hC.2.2.2.2.2
  rw [← qdecay_cast]
  exact_mod_cast hs

end
end PvNP.RealizableHardness.ZoomOutPosterior
