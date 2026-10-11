import PvNP.RealizableHardness.ActualVisiblePosteriorLedger

/-! Exact actual-joint-law composition of the visible-score posterior ledger.
The final decoder must still instantiate the explicit favorable predicate and
geometric pointwise comparison. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisibleJointSuccess
open scoped BigOperators
open PosteriorReweighting AdviceExceptions GrassmannIncidence
open TripleRestrictionRank ConditionedCovering SamplerParameters
open ZoomOutPosterior PosteriorDensity ActualVaryingCompletionException
open ActualVisiblePosteriorLedger

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A r h a : ℕ}

def goodFavorable (F : Advice (blocks A h) a → Bool)
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (Q : Advice (blocks A h) a) : Bool :=
  F Q && !(GoodAdvice.bad A h Q) &&
    !(badPosterior (beta A h) (GoodAdvice.zeta h) H Q)

theorem goodFavorable_eq_true (F : Advice (blocks A h) a → Bool)
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (Q : Advice (blocks A h) a) :
    goodFavorable F H Q = true ↔ F Q = true ∧ GoodAdvice.bad A h Q = false ∧
      badPosterior (beta A h) (GoodAdvice.zeta h) H Q = false := by
  simp [goodFavorable, and_assoc]

/-- Both advice exclusions and one actual marginal-TV cost are explicit. -/
theorem favorable_marginal_lower (haJ : a ≤ blocks A h)
    (F : Advice (blocks A h) a → Bool)
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h))) :
    mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
      mass ambientMass (badPosterior (beta A h) (GoodAdvice.zeta h) H) -
      adviceTV (beta A h) (blocks A h) a ≤
        mass (adviceMarginal (beta A h)) (goodFavorable F H) := by
  let p : Advice (blocks A h) a → ℚ := ambientMass
  have hp (Q : Advice (blocks A h) a) : 0 ≤ p Q := (ambientMass_pos Q haJ).le
  have h1 := ZoomOutJoint.mass_and_not_lower p hp F (GoodAdvice.bad (a := a) A h)
  have h2 := ZoomOutJoint.mass_and_not_lower p hp
    (fun Q => F Q && !(GoodAdvice.bad A h Q))
    (badPosterior (beta A h) (GoodAdvice.zeta h) H)
  change mass p (fun Q => F Q && !(GoodAdvice.bad A h Q)) -
    mass p (badPosterior (beta A h) (GoodAdvice.zeta h) H) ≤
      mass p (goodFavorable F H) at h2
  have ht := ambient_event_transfer (beta A h) haJ (goodFavorable F H)
  change mass p F - mass p (GoodAdvice.bad (a := a) A h) -
    mass p (badPosterior (beta A h) (GoodAdvice.zeta h) H) -
      adviceTV (beta A h) (blocks A h) a ≤ _
  linarith

def visibleEvent (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (g : Draw (blocks A h) → ℚ) (C : ℚ) (s : Draw (blocks A h)) : Bool :=
  !(excluded Q W H s) && decide (C / 4 ≤ g s)

/-- The draw is first and advice is sampled from its actual retained kernel. -/
def jointVisibleSuccess (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (g : Advice (blocks A h) a → Draw (blocks A h) → ℚ) (C : ℚ) : ℚ :=
  ∑ s : Draw (blocks A h), ∑ Q : Advice (blocks A h) a,
    if goodFavorable F H Q && visibleEvent Q (W Q) H (g Q) C s then
      joint (beta A h) s Q else 0

/-- Bayes reordering uses only advice whose actual marginal is positive. -/
theorem jointVisibleSuccess_disintegration (haJ : a ≤ blocks A h)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (g : Advice (blocks A h) a → Draw (blocks A h) → ℚ) (C : ℚ) :
    jointVisibleSuccess F W H g C = ∑ Q : Advice (blocks A h) a,
      if goodFavorable F H Q then adviceMarginal (beta A h) Q *
        mass (conditional (beta A h) Q) (visibleEvent Q (W Q) H (g Q) C) else 0 := by
  unfold jointVisibleSuccess
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hF : goodFavorable F H Q = true
  · have hgood := ((goodFavorable_eq_true F H Q).mp hF).2.1
    have hpos := (GoodAdvice.good_marginal_pos A h Q haJ hgood).2
    simp only [hF, Bool.true_and, Bool.true_eq, ite_true, mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    cases hs : visibleEvent Q (W Q) H (g Q) C s
    · simp [hs]
    · simp only [hs, Bool.true_eq, ite_true]
      exact (bayes_joint (beta A h) Q s hpos).symm.trans (mul_comm _ _)
  · have hfalse : goodFavorable F H Q = false := Bool.eq_false_iff.mpr hF
    simp [hfalse]

/-- Integrates the visible comparison in the same actual joint law. It keeps
the decoder's geometric score premise explicit until the actual application. -/
theorem ready_visible_joint_success
    (hr : SamplerProximity.Ready A r h) (hh : r < h) (ha : a ≤ r)
    (F : Advice (blocks A h) a → Bool)
    (W : Advice (blocks A h) a → Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (f : Advice (blocks A h) a → Advice (blocks A h) (2 * h) → ℚ)
    (g : Advice (blocks A h) a → Draw (blocks A h) → ℚ)
    (C loss : ℚ) (hC : 0 < C) (hloss : 0 ≤ loss)
    (hmargin : qdecay 10 h + loss + 4 * GoodAdvice.zeta h ≤ C / 2)
    (hdecoder : ∀ Q, F Q = true → Q.val ≤ W Q ∧
      SubspaceRestriction.codim (W Q) ≤ r ∧
      (∀ L, 0 ≤ f Q L ∧ f Q L ≤ 1) ∧
      C ≤ mean (ZoomOutTransfer.ambientW Q (W Q)) (f Q))
    (hg : ∀ Q s, 0 ≤ g Q s ∧ g Q s ≤ 1)
    (hcompare : ∀ Q, goodFavorable F H Q = true → ∀ s,
      excluded Q (W Q) H s = false →
        ZoomOutJoint.agreement Q (W Q) (f Q) s - loss ≤ g Q s) :
    (mass ambientMass F - mass ambientMass (GoodAdvice.bad (a := a) A h) -
      mass ambientMass (badPosterior (beta A h) (GoodAdvice.zeta h) H) -
      adviceTV (beta A h) (blocks A h) a) * (C / 4) ≤
        jointVisibleSuccess F W H g C := by
  have haJ : a ≤ blocks A h := by
    have hd := SamplerProximity.ready_dimensions hr
    omega
  have hm := favorable_marginal_lower haJ F H
  apply (mul_le_mul_of_nonneg_right hm (show 0 ≤ C / 4 by positivity)).trans
  rw [jointVisibleSuccess_disintegration haJ F W H g C, mass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro Q _
  by_cases hF : goodFavorable F H Q = true
  · have hsplit := (goodFavorable_eq_true F H Q).mp hF
    have hd := hdecoder Q hsplit.1
    have hs := ready_visible_posterior_success hr hh ha Q hsplit.2.1
      (W Q) hd.1 hd.2.1 H hsplit.2.2 (f Q) hd.2.2.1 (g Q) (hg Q)
      C loss hC hloss hd.2.2.2 (hcompare Q hF) hmargin
    simp only [hF, Bool.true_eq, ite_true]
    exact mul_le_mul_of_nonneg_left hs
      (adviceMarginal_nonneg (beta A h) (beta_nonneg A h) (beta_le_one A h) Q)
  · have hfalse : goodFavorable F H Q = false := Bool.eq_false_iff.mpr hF
    simp [hfalse]

end
end PvNP.RealizableHardness.ActualVisibleJointSuccess
