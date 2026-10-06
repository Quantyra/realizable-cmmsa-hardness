import PvNP.RealizableHardness.ZoomOutTransfer

/-! UNCOMPILED. Actual posterior decoder-score threshold and ideal joint law.
The fixed-score decoder interface is an input, not a decoder existence proof. -/
namespace PvNP.RealizableHardness.ZoomOutJoint
open scoped BigOperators
open PosteriorReweighting AdviceExceptions GrassmannIncidence
open TripleRestrictionRank ConditionedCovering SamplerParameters ZoomOutPosterior PosteriorDensity
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

section Finite
variable {X : Type*} [Fintype X]

lemma mass_and_not_lower (p : X → ℚ) (hp : ∀ x, 0 ≤ p x) (b c : X → Bool) :
    mass p b - mass p c ≤ mass p (fun x => b x && !(c x)) := by
  unfold mass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  cases hb : b x <;> cases hc : c x <;> simp [hb, hc, hp x]

/-- A bounded score with mean at least C/2 exceeds C/4 on mass at least C/4. -/
lemma score_threshold (p f : X → ℚ) (hp : ∀ x, 0 ≤ p x)
    (hn : ∑ x, p x = 1) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (C : ℚ) (hC : 0 ≤ C) (hm : C/2 ≤ mean p f) :
    C/4 ≤ mass p (fun x => decide (C/4 ≤ f x)) := by
  have hpoint (x : X) : p x * f x ≤ p x * (C/4) +
      (if decide (C/4 ≤ f x) then p x else 0) := by
    by_cases hx : C/4 ≤ f x
    · simp only [hx, decide_true, Bool.true_eq, ite_true]
      have ha := mul_le_mul_of_nonneg_left (hf x).2 (hp x)
      have hb := mul_nonneg (hp x) (show 0 ≤ C/4 by positivity)
      nlinarith
    · simp only [hx, decide_false, Bool.false_eq_true, ite_false, add_zero]
      exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hx)) (hp x)
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hn, one_mul] at hs
  change mean p f ≤ C/4 + mass p (fun x => decide (C/4 ≤ f x)) at hs
  linarith
end Finite

variable {A r h a : ℕ}

def agreement (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) (2*h) → ℚ) (s : Draw (blocks A h)) : ℚ :=
  mean (ZoomOutTransfer.retainedW s Q W) f

def succeeds (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) (2*h) → ℚ) (C : ℚ) (s : Draw (blocks A h)) : Bool :=
  decide (C/4 ≤ agreement Q W f s) &&
    !(decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W))

lemma agreement_bounds (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) (2*h) → ℚ) (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1)
    (s : Draw (blocks A h)) : 0 ≤ agreement Q W f s ∧ agreement Q W f s ≤ 1 :=
  ZoomOutTransfer.condition_score_bounds (retainedConditional s Q) f
    (retained_conditional_nonneg s Q) (ZoomOutTransfer.inW W) hf

/-- Same posterior, same W, fixed L-score. Null fibres have zero agreement. -/
theorem ready_posterior_success (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (ha : a ≤ r) (Q : Advice (blocks A h) a)
    (hQ : GoodAdvice.bad A h Q = false)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (hQW : Q.val ≤ W) (hc : SubspaceRestriction.codim W ≤ r)
    (f : Advice (blocks A h) (2*h) → ℚ) (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1)
    (C : ℚ) (hC : 0 < C) (hC1 : C ≤ 1)
    (hdelta : 2*qdecay 10 h ≤ C) (hrank : 16*GoodAdvice.zeta h ≤ C)
    (hagree : C ≤ mean (ZoomOutTransfer.ambientW Q W) f) :
    C/8 ≤ mass (conditional (beta A h) Q) (succeeds Q W f C) := by
  have hp := GoodAdvice.ready_good_properties hr ha (by omega) Q hQ
  have ht := ZoomOutTransfer.ready_transfer hr hh ha Q hp W hQW hc
  have he := ht.2.2.2.2 f hf
  have hid : mean (ZoomOutTransfer.posteriorMixture (beta A h) Q W) f =
      mean (conditional (beta A h) Q) (agreement Q W f) :=
    ZoomOutTransfer.mixture_score _ _ _
  rw [hid] at he
  have hm : C/2 ≤ mean (conditional (beta A h) Q) (agreement Q W f) := by
    have hu := le_abs_self (mean (ZoomOutTransfer.ambientW Q W) f -
      mean (conditional (beta A h) Q) (agreement Q W f))
    linarith
  have hn := conditional_normalized (beta A h) Q hp.2.2.1
  have hnon := fun s => AdviceExceptions.conditional_nonneg (beta A h)
    (beta_nonneg A h) (beta_le_one A h) Q s
  have hs := score_threshold (conditional (beta A h) Q) (agreement Q W f)
    hnon hn (agreement_bounds Q W f hf) C hC.le hm
  have hi := mass_and_not_lower (conditional (beta A h) Q) hnon
    (fun s => decide (C/4 ≤ agreement Q W f s))
    (fun s => decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W))
  have hb := hp.2.2.2.2.2.2.2 W hQW hc
  change _ ≤ mass (conditional (beta A h) Q) (succeeds Q W f C) at hi
  linarith

def favorable (F : Advice (blocks A h) a → Bool) (Q : Advice (blocks A h) a) : Bool :=
  F Q && !(GoodAdvice.bad A h Q)

/-- Favorable advice is charged under the actual marginal, with exact TV cost. -/
theorem favorable_marginal_lower (haJ : a ≤ blocks A h)
    (F : Advice (blocks A h) a → Bool) :
    mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
        adviceTV (beta A h) (blocks A h) a ≤
      mass (adviceMarginal (beta A h)) (favorable F) := by
  have hi := mass_and_not_lower (ambientMass : Advice (blocks A h) a → ℚ)
    (fun Q => (ambientMass_pos Q haJ).le) F (GoodAdvice.bad (a := a) A h)
  have ht := ambient_event_transfer (beta A h) haJ (favorable F)
  change _ ≤ mass ambientMass (favorable F) at hi
  linarith

/-- Ideal experiment: first the actual deletion draw, then uniform advice in V. -/
def jointSuccess (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) a → Advice (blocks A h) (2*h) → ℚ) (C : ℚ) : ℚ :=
  ∑ s : Draw (blocks A h), ∑ Q : Advice (blocks A h) a,
    if favorable F Q && succeeds Q (W Q) (f Q) C s then joint (beta A h) s Q else 0

/-- Exact Bayes reordering on favorable advice; positivity is proved from good advice. -/
theorem jointSuccess_disintegration (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (ha : a ≤ r)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) a → Advice (blocks A h) (2*h) → ℚ) (C : ℚ) :
    jointSuccess F W f C = ∑ Q : Advice (blocks A h) a,
      if favorable F Q then adviceMarginal (beta A h) Q *
        mass (conditional (beta A h) Q) (succeeds Q (W Q) (f Q) C) else 0 := by
  unfold jointSuccess
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hF : favorable F Q = true
  · have hgood : GoodAdvice.bad A h Q = false := by
      have hs : F Q = true ∧ GoodAdvice.bad A h Q = false := by simpa [favorable] using hF
      exact hs.2
    have hp := GoodAdvice.ready_good_properties hr ha (by omega) Q hgood
    simp only [hF, Bool.true_and, Bool.true_eq, ite_true, mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    cases hs : succeeds Q (W Q) (f Q) C s
    · simp [hs]
    · simp only [hs, Bool.true_eq, ite_true]
      exact (bayes_joint (beta A h) Q s hp.2.2.1).symm.trans (mul_comm _ _)
  · have hfalse : favorable F Q = false := Bool.eq_false_iff.mpr hF
    simp [hfalse]

/-- Decoder interface: F and its fixed scores are supplied by a separate decoder.
All posterior and joint-success conclusions below are derived for actual laws. -/
theorem ready_joint_success (hr : SamplerProximity.Ready A r h)
    (hh : r < h) (ha : a ≤ r)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) a → Advice (blocks A h) (2*h) → ℚ)
    (C : ℚ) (hC : 0 < C) (hC1 : C ≤ 1)
    (hdelta : 2*qdecay 10 h ≤ C) (hrank : 16*GoodAdvice.zeta h ≤ C)
    (hdecoder : ∀ Q, F Q = true → Q.val ≤ W Q ∧
      SubspaceRestriction.codim (W Q) ≤ r ∧
      (∀ L, 0 ≤ f Q L ∧ f Q L ≤ 1) ∧ C ≤ mean (ZoomOutTransfer.ambientW Q (W Q)) (f Q)) :
    (mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
      adviceTV (beta A h) (blocks A h) a) * (C/8) ≤ jointSuccess F W f C := by
  have haJ : a ≤ blocks A h := by have := SamplerProximity.ready_dimensions hr; omega
  have hmass := favorable_marginal_lower (A := A) (h := h) haJ F
  have hmul := mul_le_mul_of_nonneg_right hmass (show 0 ≤ C/8 by positivity)
  apply hmul.trans
  rw [jointSuccess_disintegration hr hh ha F W f C, mass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro Q _
  by_cases hF : favorable F Q = true
  · have hsplit : F Q = true ∧ GoodAdvice.bad A h Q = false := by simpa [favorable] using hF
    have hgood : GoodAdvice.bad A h Q = false := hsplit.2
    have hd := hdecoder Q hsplit.1
    have hs := ready_posterior_success hr hh ha Q hgood (W Q) hd.1 hd.2.1
      (f Q) hd.2.2.1 C hC hC1 hdelta hrank hd.2.2.2
    simp only [hF, Bool.true_eq, ite_true]
    exact mul_le_mul_of_nonneg_left hs
      (adviceMarginal_nonneg (beta A h) (beta_nonneg A h) (beta_le_one A h) Q)
  · simp [hF]

/-- The common threshold discharges readiness, not the still-external decoder. -/
theorem eventual_joint_success (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → ∀ a : ℕ, a ≤ r →
      ∀ (F : Advice (blocks A h) a → Bool)
        (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
        (f : Advice (blocks A h) a → Advice (blocks A h) (2*h) → ℚ)
        (C : ℚ), 0 < C → C ≤ 1 →
        2*qdecay 10 h ≤ C → 16*GoodAdvice.zeta h ≤ C →
        (∀ Q, F Q = true → Q.val ≤ W Q ∧
          SubspaceRestriction.codim (W Q) ≤ r ∧
          (∀ L, 0 ≤ f Q L ∧ f Q L ≤ 1) ∧
          C ≤ mean (ZoomOutTransfer.ambientW Q (W Q)) (f Q)) →
        (mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
          adviceTV (beta A h) (blocks A h) a) * (C/8) ≤ jointSuccess F W f C := by
  obtain ⟨NP, hp⟩ := SamplerProximity.eventually_ready A r hA
  refine ⟨max NP (r+1), ?_⟩
  intro h hh a ha F W f C hC hC1 hdelta hrank hd
  exact ready_joint_success (hp h (by omega)) (by omega) ha
    F W f C hC hC1 hdelta hrank hd

end
end PvNP.RealizableHardness.ZoomOutJoint
