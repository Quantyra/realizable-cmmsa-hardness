import PvNP.RealizableHardness.ZoomOutJoint
import PvNP.RealizableHardness.ActualVaryingCompletionException

/-! Finite posterior loss accounting for the visible-table comparison.
The actual laws and excluded events are instantiated here; the geometric
pointwise score comparison is the explicit remaining application premise.
Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualVisiblePosteriorLedger
open scoped BigOperators
open PosteriorReweighting AdviceExceptions GrassmannIncidence
open TripleRestrictionRank ConditionedCovering SamplerParameters
open ZoomOutPosterior PosteriorDensity ActualVaryingCompletionException

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

section Finite
variable {X : Type*} [Fintype X]

def chargedScore (g : X → ℚ) (bad : X → Bool) (x : X) : ℚ :=
  if bad x then 0 else g x

/-- Zeroing the excluded score costs its actual mass, with no independence. -/
theorem charged_mean_lower (p f g : X → ℚ) (bad : X → Bool)
    (hp : ∀ x, 0 ≤ p x) (hn : ∑ x, p x = 1)
    (hf : ∀ x, f x ≤ 1) (loss : ℚ) (hloss : 0 ≤ loss)
    (hcompare : ∀ x, bad x = false → f x - loss ≤ g x) :
    mean p f - loss - mass p bad ≤ mean p (chargedScore g bad) := by
  have hpoint (x : X) :
      p x * f x ≤ p x * chargedScore g bad x + p x * loss +
        (if bad x then p x else 0) := by
    cases hx : bad x
    · have hc := mul_le_mul_of_nonneg_left (hcompare x hx) (hp x)
      simp only [chargedScore, hx, Bool.false_eq_true, ite_false, add_zero]
      nlinarith
    · have hc := mul_le_mul_of_nonneg_left (hf x) (hp x)
      have hl := mul_nonneg (hp x) hloss
      simp only [chargedScore, hx, Bool.true_eq, ite_true, mul_zero, zero_add]
      nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hn, one_mul] at hs
  change mean p f ≤ mean p (chargedScore g bad) + loss + mass p bad at hs
  linarith

/-- A successful charged score is a nonexcluded visible score. -/
theorem visible_success_mass_lower (p f g : X → ℚ) (bad : X → Bool)
    (hp : ∀ x, 0 ≤ p x) (hn : ∑ x, p x = 1)
    (hf : ∀ x, f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (C delta loss budget : ℚ) (hC : 0 < C) (hloss : 0 ≤ loss)
    (hmean : C - delta ≤ mean p f) (hbad : mass p bad ≤ budget)
    (hcompare : ∀ x, bad x = false → f x - loss ≤ g x)
    (hmargin : delta + loss + budget ≤ C / 2) :
    C / 4 ≤ mass p (fun x => !(bad x) && decide (C / 4 ≤ g x)) := by
  have hl := charged_mean_lower p f g bad hp hn hf loss hloss hcompare
  have hm : C / 2 ≤ mean p (chargedScore g bad) := by linarith
  have hb (x : X) : 0 ≤ chargedScore g bad x ∧ chargedScore g bad x ≤ 1 := by
    cases hx : bad x <;> simp [chargedScore, hx, hg x]
  have hs := ZoomOutJoint.score_threshold p (chargedScore g bad)
    hp hn hb C hC.le hm
  have hevent : (fun x => decide (C / 4 ≤ chargedScore g bad x)) =
      (fun x => !(bad x) && decide (C / 4 ≤ g x)) := by
    funext x
    have hpos : 0 < C / 4 := by positivity
    cases hx : bad x <;> simp [chargedScore, hx, not_le.mpr hpos]
  rw [hevent] at hs
  exact hs
end Finite

variable {A r h a : ℕ}

/-- Tail, completion, rank, and zero-support exclusions for the actual draw. -/
def excluded (Q : Advice (blocks A h) a)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (s : Draw (blocks A h)) : Bool :=
  ((decide (h ^ 4 < dropCount s) || nontransverse H s Q) ||
    decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)) ||
      decide (¬ Q.val ≤ retained s)

/-- The actual posterior gives zero weight to a noncontaining draw, even at
zero marginal advice. -/
theorem conditional_zero_of_not_contained (β : ℚ)
    (Q : Advice (blocks A h) a) (s : Draw (blocks A h))
    (hs : ¬ Q.val ≤ retained s) : conditional β Q s = 0 := by
  simp [conditional, posterior, kernel, hs]

/-- All four actual excluded events cost at most four zeta in the posterior. -/
theorem excluded_mass_le (hr : SamplerProximity.Ready A r h) (ha : a ≤ r)
    (Q : Advice (blocks A h) a) (hQ : GoodAdvice.bad A h Q = false)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (hc : SubspaceRestriction.codim W ≤ r)
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (hcomp : badPosterior (beta A h) (GoodAdvice.zeta h) H Q = false) :
    mass (conditional (beta A h) Q) (excluded Q W H) ≤ 4 * GoodAdvice.zeta h := by
  let p := conditional (beta A h) Q
  let tail : Draw (blocks A h) → Bool := fun s => decide (h ^ 4 < dropCount s)
  let completion : Draw (blocks A h) → Bool := fun s => nontransverse H s Q
  let rank : Draw (blocks A h) → Bool := fun s =>
    decide (SubspaceRestriction.codimInRetained W s ≠ SubspaceRestriction.codim W)
  let unsupported : Draw (blocks A h) → Bool := fun s => decide (¬ Q.val ≤ retained s)
  have hp (s) : 0 ≤ p s :=
    AdviceExceptions.conditional_nonneg (beta A h) (beta_nonneg A h) (beta_le_one A h) Q s
  have ht : mass p tail ≤ GoodAdvice.zeta h := (GoodAdvice.good_marginal_tail A h Q hQ).2
  have hcomp' : mass p completion ≤ GoodAdvice.zeta h := by
    simpa [badPosterior, posteriorExceptionMass, p, completion, not_lt] using hcomp
  have hrank : mass p rank ≤ 2 * GoodAdvice.zeta h :=
    GoodAdvice.ready_fixed_rank_failure hr ha Q hQ W hc
  have hzero : mass p unsupported = 0 := by
    unfold mass
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : Q.val ≤ retained s
    · simp [unsupported, hs]
    · simp [unsupported, hs, p, conditional_zero_of_not_contained _ Q s hs]
  have h12 := mass_union_le p hp tail completion
  have h123 := mass_union_le p hp (fun s => tail s || completion s) rank
  have h1234 := mass_union_le p hp
    (fun s => (tail s || completion s) || rank s) unsupported
  change mass p (fun s => ((tail s || completion s) || rank s) || unsupported s) ≤ _
  linarith

/-- Actual posterior transfer with the visible-score loss included before the
threshold step. The remaining pointwise comparison is a geometric obligation,
not a supplied posterior-success or event-mass bound. -/
theorem ready_visible_posterior_success
    (hr : SamplerProximity.Ready A r h) (hh : r < h) (ha : a ≤ r)
    (Q : Advice (blocks A h) a) (hQ : GoodAdvice.bad A h Q = false)
    (W : Submodule (ZMod 2) (Vector (blocks A h)))
    (hQW : Q.val ≤ W) (hc : SubspaceRestriction.codim W ≤ r)
    (H : Draw (blocks A h) → Submodule (ZMod 2) (Vector (blocks A h)))
    (hcomp : badPosterior (beta A h) (GoodAdvice.zeta h) H Q = false)
    (f : Advice (blocks A h) (2 * h) → ℚ) (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1)
    (g : Draw (blocks A h) → ℚ) (hg : ∀ s, 0 ≤ g s ∧ g s ≤ 1)
    (C loss : ℚ) (hC : 0 < C) (hloss : 0 ≤ loss)
    (hagree : C ≤ mean (ZoomOutTransfer.ambientW Q W) f)
    (hcompare : ∀ s, excluded Q W H s = false →
      ZoomOutJoint.agreement Q W f s - loss ≤ g s)
    (hmargin : qdecay 10 h + loss + 4 * GoodAdvice.zeta h ≤ C / 2) :
    C / 4 ≤ mass (conditional (beta A h) Q)
      (fun s => !(excluded Q W H s) && decide (C / 4 ≤ g s)) := by
  have hp := GoodAdvice.ready_good_properties hr ha (by omega) Q hQ
  have ht := ZoomOutTransfer.ready_transfer hr hh ha Q hp W hQW hc
  have he := ht.2.2.2.2 f hf
  have hid : mean (ZoomOutTransfer.posteriorMixture (beta A h) Q W) f =
      mean (conditional (beta A h) Q) (ZoomOutJoint.agreement Q W f) :=
    ZoomOutTransfer.mixture_score _ _ _
  rw [hid] at he
  have hm : C - qdecay 10 h ≤
      mean (conditional (beta A h) Q) (ZoomOutJoint.agreement Q W f) := by
    have hu := le_abs_self (mean (ZoomOutTransfer.ambientW Q W) f -
      mean (conditional (beta A h) Q) (ZoomOutJoint.agreement Q W f))
    linarith
  exact visible_success_mass_lower (conditional (beta A h) Q)
    (ZoomOutJoint.agreement Q W f) g (excluded Q W H)
    (fun s => AdviceExceptions.conditional_nonneg (beta A h)
      (beta_nonneg A h) (beta_le_one A h) Q s)
    (conditional_normalized (beta A h) Q hp.2.2.1)
    (fun s => (ZoomOutJoint.agreement_bounds Q W f hf s).2) hg
    C (qdecay 10 h) loss (4 * GoodAdvice.zeta h) hC hloss hm
    (excluded_mass_le hr ha Q hQ W hc H hcomp) hcompare hmargin

end
end PvNP.RealizableHardness.ActualVisiblePosteriorLedger
