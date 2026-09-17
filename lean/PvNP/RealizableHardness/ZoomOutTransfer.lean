/- UNCOMPILED source draft. ZoomOutPosterior is a pending author dependency. -/
import PvNP.RealizableHardness.ZoomOutPosterior

namespace PvNP.RealizableHardness.ZoomOutTransfer
open scoped BigOperators
open PosteriorReweighting AdviceExceptions ConditionedCovering
open TripleRestrictionRank GrassmannIncidence PosteriorDensity
open ZoomOutIncidence ZoomOutParameters ZoomOutPosterior SamplerParameters GaussianNearOne
noncomputable section
attribute [local instance] Classical.propDecidable

section Finite
variable {X S : Type*} [Fintype X] [Fintype S]

def condition (p : X → ℚ) (b : X → Bool) (x : X) : ℚ :=
  (if b x then p x else 0) / mass p b

lemma mass_nonneg' (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b : X → Bool) : 0 ≤ mass p b := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact hp x | exact le_rfl

lemma condition_nonneg (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b : X → Bool) (x : X) :
    0 ≤ condition p b x := by
  apply div_nonneg _ (mass_nonneg' p hp b)
  split_ifs <;> first | exact hp x | exact le_rfl

lemma condition_normalized (p : X → ℚ) (b : X → Bool) (hb : 0 < mass p b) :
    ∑ x, condition p b x = 1 := by
  simp only [condition, ← Finset.sum_div]
  exact div_self (ne_of_gt hb)

lemma condition_null (p : X → ℚ) (b : X → Bool) (hb : mass p b = 0) (x : X) :
    condition p b x = 0 := by simp [condition, hb]

lemma condition_sum_le_one (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b : X → Bool) :
    ∑ x, condition p b x ≤ 1 := by
  by_cases hz : mass p b = 0
  · simp [condition_null p b hz]
  · rw [condition_normalized p b (lt_of_le_of_ne (mass_nonneg' p hp b) (Ne.symm hz))]

lemma gated_zero (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b : X → Bool)
    (hb : mass p b = 0) (x : X) : (if b x then p x else 0) = 0 := by
  have hn (y : X) : 0 ≤ (if b y then p y else 0) := by
    split_ifs <;> first | exact hp y | exact le_rfl
  have hu := Finset.single_le_sum (fun y _ => hn y) (Finset.mem_univ x)
  change (if b x then p x else 0) ≤ mass p b at hu
  rw [hb] at hu
  exact le_antisymm hu (hn x)

/-- Conditioning pays twice the original TV divided by the first event mass. -/
lemma condition_tv_mul_le (p q : X → ℚ) (hq : ∀ x, 0 ≤ q x) (b : X → Bool)
    (hpE : 0 < mass p b) (hqE : 0 < mass q b) :
    mass p b * tv (condition p b) (condition q b) ≤ 2 * tv p q := by
  let K : X → Unit → ℚ := fun x _ => if b x then 1 else 0
  have hK (x : X) (u : Unit) : 0 ≤ K x u := by dsimp [K]; split_ifs <;> norm_num
  have hm (r : X → ℚ) : marginal r K () = mass r b := by
    unfold marginal mass
    apply Finset.sum_congr rfl
    intro x _
    cases hb : b x <;> simp [K, hb]
  have hc (r : X → ℚ) : posterior r K () = condition r b := by
    funext x
    rw [posterior, hm]
    cases hb : b x <;> simp [K, condition, hb]
  have hh := fibre_conditional_tv_le p q K hq hK () (by rw [hm]; exact hpE)
    (by rw [hm]; exact hqE)
  rw [hm, hc, hc] at hh
  have hs : (∑ x, |p x * K x () - q x * K x ()|) ≤ ∑ x, |p x - q x| := by
    apply Finset.sum_le_sum
    intro x _
    cases hb : b x <;> simp [K, hb, abs_nonneg]
  exact (hh.trans hs).trans_eq (by unfold tv; ring)

lemma score_tv_le (p q f : X → ℚ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |mean p f - mean q f| ≤ 2 * tv p q := by
  have he : mean p f - mean q f = ∑ x, (p x - q x) * f x := by
    simp [mean, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ x, |(p x - q x) * f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |p x - q x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (hf x).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf x).2
    _ = _ := by unfold tv; ring

lemma condition_score_bounds (p f : X → ℚ) (hp : ∀ x, 0 ≤ p x)
    (b : X → Bool) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ mean (condition p b) f ∧ mean (condition p b) f ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (condition_nonneg p hp b x) (hf x).1
  · calc
      _ ≤ ∑ x, condition p b x := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_of_le_one_right (condition_nonneg p hp b x) (hf x).2
      _ ≤ 1 := condition_sum_le_one p hp b

lemma mixture_event_mass (r : S → ℚ) (K : S → X → ℚ) (b : X → Bool) :
    mass (fun x => ∑ s, r s * K s x) b = normalizer r (fun s => mass (K s) b) := by
  calc
    _ = ∑ x, ∑ s, r s * (if b x then K s x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases hb : b x <;> simp [hb]
    _ = _ := by rw [Finset.sum_comm]; simp [normalizer, mass, Finset.mul_sum]

/-- Exact disintegration includes zero event fibres; no normalized kernel premise. -/
lemma condition_mixture (r : S → ℚ) (K : S → X → ℚ) (hK : ∀ s x, 0 ≤ K s x)
    (b : X → Bool) (hZ : 0 < normalizer r (fun s => mass (K s) b)) (x : X) :
    condition (fun y => ∑ s, r s * K s y) b x =
      ∑ s, (r s * mass (K s) b / normalizer r (fun t => mass (K t) b)) *
        condition (K s) b x := by
  have he (s : S) :
      (r s * mass (K s) b / normalizer r (fun t => mass (K t) b)) * condition (K s) b x =
        r s * (if b x then K s x else 0) / normalizer r (fun t => mass (K t) b) := by
    by_cases hz : mass (K s) b = 0
    · rw [gated_zero (K s) (hK s) b hz x]
      simp [hz]
    · unfold condition
      field_simp [hz, ne_of_gt hZ] <;> ring
  simp only [he, ← Finset.sum_div]
  rw [condition, mixture_event_mass]
  congr 1
  cases hb : b x <;> simp [hb]

lemma mixture_score (r : S → ℚ) (K : S → X → ℚ) (f : X → ℚ) :
    mean (fun x => ∑ s, r s * K s x) f = mean r (fun s => mean (K s) f) := by
  unfold mean
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  ring
end Finite

variable {J a d : ℕ}

def inW (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (L : Advice J d) : Bool :=
  decide (L.val ≤ W)

def ambientW (Q : Advice J a) (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    Advice J d → ℚ := condition (ambientConditional Q) (inW W)
def deletedW (β : ℚ) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) : Advice J d → ℚ :=
  condition (deletedConditional β Q) (inW W)
def retainedW (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) : Advice J d → ℚ :=
  condition (retainedConditional s Q) (inW W)

def posteriorMixture (β : ℚ) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) (L : Advice J d) : ℚ :=
  ∑ s, conditional β Q s * retainedW s Q W L

lemma retained_event_mass_eq (s : Draw J) (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    mass (retainedConditional (d := d) s Q) (inW W) = retainedZoomMass s Q W d := by
  simp [mass, inW, retainedZoomMass]

lemma ambient_event_mass_eq (Q : Advice J a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    mass (ambientConditional (d := d) Q) (inW W) = ambientZoomMass Q W d := by
  simp [mass, inW, ambientZoomMass]

lemma deleted_event_eq_normalizer (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (Q : Advice J a) (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J))
    (had : a ≤ d) (hdJ : d ≤ J) :
    mass (deletedConditional (d := d) β Q) (inW W) =
      normalizer (conditional β Q) (fun s => retainedZoomMass s Q W d) := by
  have hf : deletedConditional (d := d) β Q =
      fun L => ∑ s, conditional β Q s * retainedConditional s Q L := by
    funext L
    exact deletedConditional_eq_advicePosterior_mixture β hβ hβ1 Q L had hdJ
  rw [hf, mixture_event_mass]
  simp only [retained_event_mass_eq]

lemma exact_disintegration {A h : ℕ} (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (had : a ≤ 2*h) (hdJ : 2*h ≤ blocks A h)
    (hZ : 0 < normalizer (conditional (beta A h) Q) (fun s => retainedZoomMass s Q W (2*h)))
    (L : Advice (blocks A h) (2*h)) :
    deletedW (beta A h) Q W L = ∑ s, reweighted A h Q W s * retainedW s Q W L := by
  have hf : deletedConditional (d := 2*h) (beta A h) Q =
      fun L => ∑ s, conditional (beta A h) Q s * retainedConditional s Q L := by
    funext R
    exact deletedConditional_eq_advicePosterior_mixture (beta A h)
      (beta_nonneg A h) (beta_lt_one A h) Q R had hdJ
  unfold deletedW
  rw [hf]
  have hZ' : 0 < normalizer (conditional (beta A h) Q)
      (fun s => mass (retainedConditional (d := 2*h) s Q) (inW W)) := by
    simpa only [retained_event_mass_eq] using hZ
  have he := condition_mixture (conditional (beta A h) Q) (fun s L => retainedConditional s Q L)
    (fun s L => retained_conditional_nonneg s Q L) (inW W) hZ' L
  simpa only [retained_event_mass_eq, reweighted, retainedW] using he

lemma ambient_codim_dimension (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector J)) :
    Module.finrank (ZMod 2) W + SubspaceRestriction.codim W = 3*J := by
  have he : Module.finrank (ZMod 2) (TripleRestrictionRank.Vector J) = 3*J := by
    simp [TripleRestrictionRank.Vector, Coord, Nat.mul_comm]
  have hl := W.finrank_le
  rw [he] at hl
  unfold SubspaceRestriction.codim
  rw [he]
  omega

lemma total_error_small {r h a c : ℕ} (hh : r < h) (hc : c ≤ r) :
    8*qdecay 100 h/leading (2*h-a) c + qdecay 12 h < qdecay 10 h := by
  have hz : qdecay 100 h ≤ GoodAdvice.zeta h := by
    unfold qdecay GoodAdvice.zeta
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hdiv := (div_le_div_of_nonneg_right hz (leading_pos _ _).le).trans
    (zeta_div_le_decay20 (a := a) hh hc)
  have hsq : 1 ≤ h^2 := one_le_pow₀ (show 1 ≤ h by omega)
  have h10 : qdecay 10 h ≤ (1/2 : ℚ)^4 := by
    unfold qdecay
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : qdecay 2 h ≤ (1/2 : ℚ)^2 := by
    unfold qdecay
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he20 : qdecay 20 h = qdecay 10 h * qdecay 10 h := by
    unfold qdecay
    rw [← pow_add]
    congr 1 <;> omega
  have he12 : qdecay 12 h = qdecay 10 h * qdecay 2 h := by
    unfold qdecay
    rw [← pow_add]
    congr 1 <;> omega
  have hp : 0 < qdecay 10 h := by unfold qdecay; positivity
  rw [he20] at hdiv
  rw [he12]
  norm_num at h10 h2
  have hm10 := mul_le_mul_of_nonneg_left h10 hp.le
  have hm2 := mul_le_mul_of_nonneg_left h2 hp.le
  have he8 : 8*qdecay 100 h/leading (2*h-a) c =
      8*(qdecay 100 h/leading (2*h-a) c) := by ring
  rw [he8]
  nlinarith

def Conclusion (A h a : ℕ) (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h))) : Prop :=
  let p0 := leading (2*h-a) (SubspaceRestriction.codim W)
  p0/2 ≤ ambientZoomMass Q W (2*h) ∧
  0 < mass (deletedConditional (d := 2*h) (beta A h) Q) (inW W) ∧
  tv (ambientW (d := 2*h) Q W) (deletedW (beta A h) Q W) ≤ 4*qdecay 100 h/p0 ∧
  (∀ L : Advice (blocks A h) (2*h),
    deletedW (beta A h) Q W L = ∑ s, reweighted A h Q W s * retainedW s Q W L) ∧
  (∀ f : Advice (blocks A h) (2*h) → ℚ, (∀ L, 0 ≤ f L ∧ f L ≤ 1) →
    |mean (ambientW Q W) f - mean (posteriorMixture (beta A h) Q W) f| < qdecay 10 h)

theorem ready_transfer {A r h a : ℕ} (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (ha : a ≤ r) (Q : Advice (blocks A h) a)
    (hprops : GoodAdvice.Properties A r h a Q)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hQW : Q.val ≤ W) (hc : SubspaceRestriction.codim W ≤ r) : Conclusion A h a Q W := by
  have hd := SamplerProximity.ready_dimensions hr
  have had : a ≤ 2*h := by omega
  have hab := ambient_bounds hh (ready_budget hr) ha hc Q W hQW (ambient_codim_dimension W)
  have hpost := ZoomOutPosterior.ready_comparison hr hh ha Q hprops W hQW hc
  have hp0 := leading_pos (2*h-a) (SubspaceRestriction.codim W)
  have hpE : 0 < mass (ambientConditional (d := 2*h) Q) (inW W) := by
    rw [ambient_event_mass_eq]
    linarith [hab.2.2.2.2]
  have hqE : 0 < mass (deletedConditional (d := 2*h) (beta A h) Q) (inW W) := by
    rw [deleted_event_eq_normalizer (beta A h) (beta_nonneg A h) (beta_lt_one A h) Q W had hd.2]
    exact hpost.2.1
  have hq (L : Advice (blocks A h) (2*h)) : 0 ≤ deletedConditional (beta A h) Q L := by
    unfold deletedConditional posterior
    apply div_nonneg
    · exact mul_nonneg (adviceMarginal_nonneg _ (beta_nonneg A h) (beta_le_one A h) L)
        (flagKernel_nonneg L Q)
    · exact marginal_nonneg _ _
        (adviceMarginal_nonneg _ (beta_nonneg A h) (beta_le_one A h)) flagKernel_nonneg Q
  have htv := condition_tv_mul_le (ambientConditional (d := 2*h) Q)
    (deletedConditional (beta A h) Q) hq (inW W) hpE hqE
  have hDelta : tv (ambientConditional (d := 2*h) Q) (deletedConditional (beta A h) Q) ≤
      qdecay 100 h := by
    have h := hprops.2.2.2.2.1
    rw [← qdecay_cast] at h
    exact_mod_cast h
  have htv0 := tv_nonneg (ambientW (d := 2*h) Q W) (deletedW (beta A h) Q W)
  have htvbound : tv (ambientW (d := 2*h) Q W) (deletedW (beta A h) Q W) ≤
      4*qdecay 100 h / leading (2*h-a) (SubspaceRestriction.codim W) := by
    apply (le_div_iff₀ hp0).mpr
    rw [ambient_event_mass_eq] at htv
    change ambientZoomMass Q W (2*h) * tv (ambientW Q W) (deletedW (beta A h) Q W) ≤ _ at htv
    nlinarith [hab.2.2.2.2]
  refine ⟨hab.2.2.2.2, hqE, htvbound,
    fun L => exact_disintegration Q W had hd.2 hpost.2.1 L, ?_⟩
  intro f hf
  let F : Draw (blocks A h) → ℚ := fun s => mean (retainedW s Q W) f
  have hF (s : Draw (blocks A h)) : 0 ≤ F s ∧ F s ≤ 1 :=
    condition_score_bounds (retainedConditional s Q) f
      (retained_conditional_nonneg s Q) (inW W) hf
  have hrew : mean (deletedW (beta A h) Q W) f = mean (reweighted A h Q W) F := by
    have he : deletedW (d := 2*h) (beta A h) Q W =
        fun L => ∑ s, reweighted A h Q W s * retainedW s Q W L := by
      funext L
      exact exact_disintegration Q W had hd.2 hpost.2.1 L
    rw [he, mixture_score]
  have hun : mean (posteriorMixture (beta A h) Q W) f = mean (conditional (beta A h) Q) F :=
    mixture_score _ _ _
  have hs := score_tv_le (ambientW Q W) (deletedW (beta A h) Q W) f hf
  have hm := (hpost.2.2.2.2.1 F hF).trans_lt hpost.2.2.2.2.2
  have htriangle := abs_sub_le (mean (ambientW Q W) f) (mean (deletedW (beta A h) Q W) f)
    (mean (posteriorMixture (beta A h) Q W) f)
  rw [hrew, hun, abs_sub_comm (mean (reweighted A h Q W) F)] at htriangle
  have hn := total_error_small (a := a) hh hc
  have hsbound := hs.trans (mul_le_mul_of_nonneg_left htvbound (by norm_num : (0 : ℚ) ≤ 2))
  have he8 : 2*(4*qdecay 100 h/leading (2*h-a) (SubspaceRestriction.codim W)) =
      8*qdecay 100 h/leading (2*h-a) (SubspaceRestriction.codim W) := by ring
  rw [he8, hrew] at hsbound
  rw [hun]
  linarith

/-- Actual L transfer with all numerical and exceptional-probability premises discharged. -/
theorem eventual_transfer (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → ∀ a : ℕ, a ≤ r →
      ∀ Q : Advice (blocks A h) a, GoodAdvice.bad A h Q = false →
      ∀ W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)),
        Q.val ≤ W → SubspaceRestriction.codim W ≤ r → Conclusion A h a Q W := by
  obtain ⟨NG, _, hg⟩ := GoodAdvice.eventual_good_advice A r hA
  obtain ⟨NP, hp⟩ := SamplerProximity.eventually_ready A r hA
  refine ⟨max NG NP, ?_⟩
  intro h hh a ha Q hQ W hQW hc
  have hgood := hg h (show NG ≤ h by omega)
  exact ready_transfer (hp h (by omega)) hgood.1 ha Q ((hgood.2.2 a ha).2.2 Q hQ) W hQW hc

theorem conclusion_event {A h a : ℕ} (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hC : Conclusion A h a Q W) (b : Advice (blocks A h) (2*h) → Bool) :
    |mass (ambientW Q W) b - mass (posteriorMixture (beta A h) Q W) b| < qdecay 10 h := by
  have he (p : Advice (blocks A h) (2*h) → ℚ) : mean p (fun L => if b L then 1 else 0) = mass p b := by
    unfold mean mass
    apply Finset.sum_congr rfl
    intro L _
    cases hb : b L <;> simp [hb]
  have hh := hC.2.2.2.2 (fun L => if b L then 1 else 0)
    (fun L => by cases b L <;> norm_num)
  simpa only [he] using hh

/-- Constant-one scores explicitly account for lost mass at null retained fibres. -/
theorem conclusion_mass_defect {A h a : ℕ} (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hC : Conclusion A h a Q W) :
    |1 - ∑ L : Advice (blocks A h) (2*h), posteriorMixture (beta A h) Q W L| < qdecay 10 h := by
  have hp : 0 < mass (ambientConditional (d := 2*h) Q) (inW W) := by
    rw [ambient_event_mass_eq]
    have hpos := leading_pos (2*h-a) (SubspaceRestriction.codim W)
    linarith [hC.1]
  have hn : (∑ L : Advice (blocks A h) (2*h), ambientW Q W L) = 1 :=
    condition_normalized _ _ hp
  have hs := hC.2.2.2.2 (fun _ => 1) (fun _ => by norm_num)
  simpa only [mean, mul_one, hn] using hs

theorem conclusion_score_real {A h a : ℕ} (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (TripleRestrictionRank.Vector (blocks A h)))
    (hC : Conclusion A h a Q W) (f : Advice (blocks A h) (2*h) → ℚ)
    (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1) :
    ((|mean (ambientW Q W) f - mean (posteriorMixture (beta A h) Q W) f| : ℚ) : ℝ) <
      DropTailParameters.decay 10 h := by
  rw [← qdecay_cast]
  exact_mod_cast hC.2.2.2.2 f hf

end
end PvNP.RealizableHardness.ZoomOutTransfer
