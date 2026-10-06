/- UNCOMPILED source draft. No author build or independent acceptance claimed. -/
import PvNP.RealizableHardness.CoveringSpan
import PvNP.RealizableHardness.GrassmannFlagPosterior
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! KMS Lemma 4.7 via the actual finite flag sampler. The two distributions
are conditioned on containment, not on an independently resampled deletion.
The proof follows the source's conditional-TV averaging argument. -/
namespace PvNP.RealizableHardness.ConditionedCovering
open scoped BigOperators
open TripleRestrictionRank GrassmannIncidence GrassmannCounting
open GrassmannFlagPosterior PosteriorDensity PosteriorReweighting
noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteConditioning
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Conditional TV multiplied by the first marginal is bounded by the full
L1 discrepancy in that fibre. Both positive conditioning events are explicit. -/
lemma fibre_conditional_tv_le (p q : X → ℚ) (K : X → Y → ℚ)
    (hq : ∀ x, 0 ≤ q x) (hK : ∀ x y, 0 ≤ K x y) (y : Y)
    (hpY : 0 < marginal p K y) (hqY : 0 < marginal q K y) :
    marginal p K y * AdviceExceptions.tv (posterior p K y) (posterior q K y) ≤
      ∑ x, |p x * K x y - q x * K x y| := by
  have hn := posterior_normalized q K y hqY
  have hpost (x : X) : 0 ≤ posterior q K y x :=
    div_nonneg (mul_nonneg (hq x) (hK x y)) hqY.le
  have hpoint (x : X) :
      marginal p K y * |posterior p K y x - posterior q K y x| ≤
        |p x * K x y - q x * K x y| +
          |marginal q K y - marginal p K y| * posterior q K y x := by
    have hid : marginal p K y * (posterior p K y x - posterior q K y x) =
        (p x * K x y - q x * K x y) +
          (marginal q K y - marginal p K y) * posterior q K y x := by
      have hpB := bayes_mass p K y x hpY
      have hqB := bayes_mass q K y x hqY
      nlinarith
    calc
      _ = |marginal p K y * (posterior p K y x - posterior q K y x)| := by
        rw [abs_mul, abs_of_pos hpY]
      _ = _ := congrArg abs hid
      _ ≤ _ := by
        simpa only [abs_mul, abs_of_nonneg (hpost x)] using
          abs_add_le (p x * K x y - q x * K x y)
            ((marginal q K y - marginal p K y) * posterior q K y x)
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hn, mul_one] at hs
  have hm : |marginal q K y - marginal p K y| ≤
      ∑ x, |p x * K x y - q x * K x y| := by
    rw [abs_sub_comm]
    unfold marginal
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  unfold AdviceExceptions.tv
  nlinarith

/-- Average conditional-TV loss is at most twice the unconditioned TV.
K is an actual shared normalized nonnegative kernel. -/
theorem conditional_tv_average_le (p q : X → ℚ) (K : X → Y → ℚ)
    (hq : ∀ x, 0 ≤ q x) (hK : ∀ x y, 0 ≤ K x y)
    (hKn : ∀ x, ∑ y, K x y = 1)
    (hpY : ∀ y, 0 < marginal p K y) (hqY : ∀ y, 0 < marginal q K y) :
    (∑ y, marginal p K y *
      AdviceExceptions.tv (posterior p K y) (posterior q K y)) ≤
        2 * AdviceExceptions.tv p q := by
  calc
    _ ≤ ∑ y, ∑ x, |p x * K x y - q x * K x y| :=
      Finset.sum_le_sum fun y _ => fibre_conditional_tv_le p q K hq hK y (hpY y) (hqY y)
    _ = ∑ x, |p x - q x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [← sub_mul, abs_mul, abs_of_nonneg (hK x _), ← Finset.mul_sum, hKn, mul_one]
    _ = _ := by unfold AdviceExceptions.tv; ring

end FiniteConditioning

variable {J a d : ℕ}

/-- Uniform a-space inside the actual d-space L. -/
def flagKernel (L : Advice J d) (Q : Advice J a) : ℚ :=
  if Q.val ≤ L.val then (gaussian d a : ℚ)⁻¹ else 0

lemma flagKernel_nonneg (L : Advice J d) (Q : Advice J a) : 0 ≤ flagKernel L Q := by
  unfold flagKernel
  split_ifs <;> positivity

lemma flagKernel_normalized (had : a ≤ d) (L : Advice J d) :
    ∑ Q : Advice J a, flagKernel L Q = 1 := by
  have hc : (gaussian d a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (GaussianRatio.gaussian_pos had))
  have hl : (∑ Q : Advice J a, if Q.val ≤ L.val then (1 : ℚ) else 0) = gaussian d a := by
    have hn : (∑ Q : Advice J a, if Q.val ≤ L.val then (1 : ℕ) else 0) = gaussian d a := by
      let e : Advice J a ≃ Grass (TripleRestrictionRank.Vector J) a := Equiv.refl _
      calc
        _ = ∑ Q : Grass (TripleRestrictionRank.Vector J) a,
            if Q.val ≤ L.val then (1 : ℕ) else 0 :=
          e.sum_comp (fun Q => if Q.val ≤ L.val then (1 : ℕ) else 0)
        _ = _ := lowerCount (a := a) L
    exact_mod_cast hn
  calc
    _ = (∑ Q : Advice J a, if Q.val ≤ L.val then (1 : ℚ) else 0) *
        (gaussian d a : ℚ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Q _
      by_cases h : Q.val ≤ L.val <;> simp [flagKernel, h]
    _ = 1 := by rw [hl, mul_inv_cancel₀ hc]

lemma ambient_flag_marginal (Q : Advice J a) (had : a ≤ d) (hdJ : d ≤ J) :
    marginal (ambientMass : Advice J d → ℚ) flagKernel Q = ambientMass Q := by
  have hn : Module.finrank (ZMod 2) (TripleRestrictionRank.Vector J) = 3 * J := by
    simp [TripleRestrictionRank.Vector, Coord, Module.finrank_pi, Nat.mul_comm]
  have ha : gaussian (Module.finrank (ZMod 2) (TripleRestrictionRank.Vector J)) a ≠ 0 := by
    rw [hn]
    exact Nat.ne_of_gt (GaussianRatio.gaussian_pos (show a ≤ 3 * J by omega))
  have hd : gaussian (Module.finrank (ZMod 2) (TripleRestrictionRank.Vector J)) d ≠ 0 := by
    rw [hn]
    exact Nat.ne_of_gt (GaussianRatio.gaussian_pos (show d ≤ 3 * J by omega))
  have hr := upperCount_ratio Q had ha hd
  rw [hn] at hr
  have hc : (gaussian d a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (GaussianRatio.gaussian_pos had))
  have hu : (∑ L : Advice J d, if Q.val ≤ L.val then (1 : ℚ) else 0) = upperCount Q d := by
    have hn' : (∑ L : Advice J d, if Q.val ≤ L.val then (1 : ℕ) else 0) = upperCount Q d := by
      let e : Advice J d ≃ Grass (TripleRestrictionRank.Vector J) d := Equiv.refl _
      exact e.sum_comp (fun L => if Q.val ≤ L.val then (1 : ℕ) else 0)
    exact_mod_cast hn'
  calc
    _ = ((upperCount Q d : ℚ) / gaussian (3 * J) d) / gaussian d a := by
      unfold marginal
      rw [← hu]
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro L _
      by_cases h : Q.val ≤ L.val <;> simp [flagKernel, h, ambientMass_eq, div_eq_mul_inv]
    _ = _ := by rw [hr, ambientMass_eq]; field_simp [hc]

lemma retained_flag_marginal (s : Draw J) (Q : Advice J a)
    (had : a ≤ d) (hdJ : d ≤ J) :
    marginal (kernel s : Advice J d → ℚ) flagKernel Q = kernel s Q := by
  have hc : (gaussian d a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (GaussianRatio.gaussian_pos had))
  calc
    _ = containmentProbability s d Q / gaussian d a := by
      unfold marginal containmentProbability
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro L _
      by_cases h : Q.val ≤ L.val <;> simp [flagKernel, h, div_eq_mul_inv]
    _ = _ := by rw [containmentProbability_formula s d Q had hdJ]; field_simp [hc]

/-- Actual flag disintegration: no joint-law equality is assumed. -/
lemma deleted_flag_marginal (β : ℚ) (Q : Advice J a) (had : a ≤ d) (hdJ : d ≤ J) :
    marginal (adviceMarginal β : Advice J d → ℚ) flagKernel Q = adviceMarginal β Q := by
  unfold marginal adviceMarginal PosteriorReweighting.marginal
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have h := retained_flag_marginal s Q had hdJ
  unfold marginal at h
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h]

/-- The no-deletion atom ensures all actual advice conditioning events are positive. -/
lemma adviceMarginal_pos (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (Q : Advice J a) (ha : a ≤ J) : 0 < adviceMarginal β Q := by
  let s : Draw J := fun _ => none
  have hs : 0 < prior β s := by
    unfold prior FiniteSampling.trialMass
    apply Finset.prod_pos
    intro j _
    change 0 < 1 - β
    linarith
  have ht : retained s = ⊤ := by
    apply CoveringSpan.retained_eq_top_of_no_drop
    simp [TripleRestrictionDimension.dropCount, s]
  have hk : 0 < kernel s Q := (kernel_pos_iff s Q ha).mpr (by rw [ht]; exact le_top)
  have hle : prior β s * kernel s Q ≤ adviceMarginal β Q :=
    Finset.single_le_sum (fun t _ => joint_nonneg β hβ hβ1.le t Q) (Finset.mem_univ s)
  exact lt_of_lt_of_le (mul_pos hs hk) hle

/-- These are the actual L laws conditioned on Q≤L; null-event convention is zero. -/
def ambientConditional (Q : Advice J a) (L : Advice J d) : ℚ :=
  posterior ambientMass flagKernel Q L

def deletedConditional (β : ℚ) (Q : Advice J a) (L : Advice J d) : ℚ :=
  posterior (adviceMarginal β) flagKernel Q L

lemma ambientConditional_normalized (Q : Advice J a) (had : a ≤ d) (hdJ : d ≤ J) :
    ∑ L : Advice J d, ambientConditional Q L = 1 := by
  apply posterior_normalized
  rw [ambient_flag_marginal Q had hdJ]
  exact ambientMass_pos Q (had.trans hdJ)

lemma deletedConditional_normalized (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (Q : Advice J a) (had : a ≤ d) (hdJ : d ≤ J) :
    ∑ L : Advice J d, deletedConditional β Q L = 1 := by
  apply posterior_normalized
  rw [deleted_flag_marginal β Q had hdJ]
  exact adviceMarginal_pos β hβ hβ1 Q (had.trans hdJ)

lemma ambientConditional_formula (Q : Advice J a) (L : Advice J d)
    (had : a ≤ d) (hdJ : d ≤ J) :
    ambientConditional Q L = (if Q.val ≤ L.val then ambientMass L else 0) /
      ((gaussian d a : ℚ) * ambientMass Q) := by
  unfold ambientConditional posterior
  rw [ambient_flag_marginal Q had hdJ]
  by_cases h : Q.val ≤ L.val
  · simp only [flagKernel, h, ite_true, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [flagKernel, h]

/-- Exact global-containment conditional law, with the actual deletion event mass. -/
lemma deletedConditional_formula (β : ℚ) (Q : Advice J a) (L : Advice J d)
    (had : a ≤ d) (hdJ : d ≤ J) :
    deletedConditional β Q L =
      (if Q.val ≤ L.val then adviceMarginal β L else 0) / eventMarginal β d Q := by
  have hc : (gaussian d a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (GaussianRatio.gaussian_pos had))
  unfold deletedConditional posterior
  rw [deleted_flag_marginal β Q had hdJ, eventMarginal_formula β d Q had hdJ]
  by_cases h : Q.val ≤ L.val
  · simp only [flagKernel, h, ite_true]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [flagKernel, h]

/-- Uniform L inside the retained space, then conditioned on containing Q. -/
def retainedConditional (s : Draw J) (Q : Advice J a) (L : Advice J d) : ℚ :=
  (if Q.val ≤ L.val then kernel s L else 0) / containmentProbability s d Q

lemma retainedConditional_normalized (s : Draw J) (Q : Advice J a)
    (hpos : 0 < containmentProbability s d Q) :
    ∑ L : Advice J d, retainedConditional s Q L = 1 := by
  unfold retainedConditional
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

lemma contained_kernel_zero (s : Draw J) (Q : Advice J a) (L : Advice J d)
    (hz : containmentProbability s d Q = 0) :
    (if Q.val ≤ L.val then kernel s L else 0) = 0 := by
  have hn (R : Advice J d) : 0 ≤ (if Q.val ≤ R.val then kernel s R else 0) := by
    split_ifs <;> first | exact kernel_nonneg _ _ | exact le_rfl
  have hle : (if Q.val ≤ L.val then kernel s L else 0) ≤ containmentProbability s d Q :=
    Finset.single_le_sum (fun R _ => hn R) (Finset.mem_univ L)
  exact le_antisymm (hz ▸ hle) (hn L)

/-- Exact global-conditioning disintegration into the actual posterior V law
and the actual uniform L-in-V law conditioned on Q. Null V fibres contribute zero. -/
theorem deletedConditional_eq_eventPosterior_mixture (β : ℚ)
    (Q : Advice J a) (L : Advice J d) (had : a ≤ d) (hdJ : d ≤ J) :
    deletedConditional β Q L =
      ∑ s : Draw J, eventPosterior β d Q s * retainedConditional s Q L := by
  rw [deletedConditional_formula β Q L had hdJ]
  have hpoint (s : Draw J) :
      eventPosterior β d Q s * retainedConditional s Q L =
        prior β s * (if Q.val ≤ L.val then kernel s L else 0) / eventMarginal β d Q := by
    by_cases hz : containmentProbability s d Q = 0
    · rw [retainedConditional, hz, div_zero, mul_zero, contained_kernel_zero s Q L hz]
      simp
    · unfold eventPosterior retainedConditional
      by_cases he : eventMarginal β d Q = 0
      · simp [he]
      · field_simp [hz, he]
        <;> ring
  simp only [hpoint, ← Finset.sum_div]
  congr 1
  by_cases h : Q.val ≤ L.val
  · simp only [h, ite_true]
    rfl
  · simp [h]

/-- The imported flag theorem identifies this very posterior with the advice
posterior already used in the density and tail estimates. -/
theorem deletedConditional_eq_advicePosterior_mixture (β : ℚ) (hβ : 0 ≤ β)
    (hβ1 : β < 1) (Q : Advice J a) (L : Advice J d)
    (had : a ≤ d) (hdJ : d ≤ J) :
    deletedConditional β Q L =
      ∑ s : Draw J, conditional β Q s * retainedConditional s Q L := by
  have hc : (0 : ℚ) < gaussian d a := by
    exact_mod_cast GaussianRatio.gaussian_pos had
  have hm : 0 < eventMarginal β d Q := by
    rw [eventMarginal_formula β d Q had hdJ]
    exact mul_pos hc (adviceMarginal_pos β hβ hβ1 Q (had.trans hdJ))
  rw [deletedConditional_eq_eventPosterior_mixture β Q L had hdJ]
  apply Finset.sum_congr rfl
  intro s _
  rw [eventPosterior_eq_conditional β d Q had hdJ hm s]

def conditionalDistance (β : ℚ) (Q : Advice J a) : ℚ :=
  AdviceExceptions.tv (ambientConditional (d := d) Q) (deletedConditional β Q)

lemma conditionalDistance_nonneg (β : ℚ) (Q : Advice J a) :
    0 ≤ conditionalDistance (d := d) β Q := AdviceExceptions.tv_nonneg _ _

/-- KMS's expectation bound instantiated with actual Grassmann incidence laws. -/
theorem actual_conditional_average_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (had : a ≤ d) (hdJ : d ≤ J) :
    (∑ Q : Advice J a, ambientMass Q * conditionalDistance (d := d) β Q) ≤
      2 * AdviceExceptions.tv (ambientMass : Advice J d → ℚ) (adviceMarginal β) := by
  have h := conditional_tv_average_le (ambientMass : Advice J d → ℚ) (adviceMarginal β)
    (flagKernel (a := a)) (adviceMarginal_nonneg β hβ hβ1.le) flagKernel_nonneg
    (flagKernel_normalized had)
    (fun Q => by rw [ambient_flag_marginal Q had hdJ]; exact ambientMass_pos Q (had.trans hdJ))
    (fun Q => by rw [deleted_flag_marginal β Q had hdJ]; exact adviceMarginal_pos β hβ hβ1 Q (had.trans hdJ))
  change (∑ Q : Advice J a, ambientMass Q * AdviceExceptions.tv
    (posterior (ambientMass : Advice J d → ℚ) flagKernel Q)
    (posterior (adviceMarginal β : Advice J d → ℚ) flagKernel Q)) ≤ _
  simpa only [ambient_flag_marginal _ had hdJ] using h

def zoomError (β : ℚ) (J : ℕ) : ℝ := Real.sqrt (β : ℝ) * Real.sqrt (Real.sqrt J)

lemma zoomError_nonneg (β : ℚ) (J : ℕ) : 0 ≤ zoomError β J := by
  unfold zoomError
  positivity

lemma zoomError_sq (β : ℚ) (hβ : 0 ≤ β) (J : ℕ) :
    zoomError β J ^ 2 = (β : ℝ) * Real.sqrt J := by
  unfold zoomError
  rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hβ), Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma zoomError_eq_source (β : ℚ) (J : ℕ) :
    zoomError β J = Real.sqrt (β : ℝ) * (J : ℝ) ^ (1 / 4 : ℝ) := by
  unfold zoomError
  rw [Real.sqrt_eq_rpow (Real.sqrt J), Real.sqrt_eq_rpow (J : ℝ),
    ← Real.rpow_mul (Nat.cast_nonneg J)]
  norm_num

theorem actual_conditional_average_le_real (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (had : a ≤ d) (hdJ : d ≤ J) :
    (∑ Q : Advice J a, (ambientMass Q : ℝ) * (conditionalDistance (d := d) β Q : ℝ)) ≤
      zoomError β J ^ 2 * (2 : ℝ)^(d + 5) := by
  have h : (∑ Q : Advice J a, (ambientMass Q : ℝ) * (conditionalDistance (d := d) β Q : ℝ)) ≤
      2 * (AdviceExceptions.tv (ambientMass : Advice J d → ℚ) (adviceMarginal β) : ℝ) := by
    exact_mod_cast actual_conditional_average_le β hβ hβ1 had hdJ
  have hc := CoveringSpan.actual_adviceTV_le_manuscript β hβ hβ1.le hdJ
  rw [zoomError_sq β hβ J]
  have hp : (2 : ℝ)^(d+5) = 2 * (2 : ℝ)^(d+4) := by
    rw [show d+5 = (d+4)+1 by omega, pow_succ]; ring
  rw [hp]
  nlinarith

def badZoom (β : ℚ) (Q : Advice J a) : Bool :=
  decide (zoomError β J * (2 : ℝ)^(d+5) < (conditionalDistance (d := d) β Q : ℝ))

/-- Actual uniform-Q exceptional probability, including the zero-error boundary.
The proof does not divide by the error until positivity has been established. -/
theorem badZoom_mass_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (had : a ≤ d) (hdJ : d ≤ J) :
    (mass (ambientMass : Advice J a → ℚ) (badZoom (d := d) β) : ℝ) ≤ zoomError β J := by
  have hav := actual_conditional_average_le_real β hβ hβ1 had hdJ
  have he := zoomError_nonneg β J
  have hw (Q : Advice J a) : (0 : ℝ) < ambientMass Q := by
    exact_mod_cast ambientMass_pos Q (had.trans hdJ)
  have hd0 (Q : Advice J a) : (0 : ℝ) ≤ conditionalDistance (d := d) β Q := by
    exact_mod_cast conditionalDistance_nonneg (d := d) β Q
  by_cases hz : zoomError β J = 0
  · have hzero (Q : Advice J a) : (conditionalDistance (d := d) β Q : ℝ) = 0 := by
      have hle : (ambientMass Q : ℝ) * (conditionalDistance (d := d) β Q : ℝ) ≤
          ∑ R : Advice J a, (ambientMass R : ℝ) * (conditionalDistance (d := d) β R : ℝ) :=
        Finset.single_le_sum (fun R _ => mul_nonneg (hw R).le (hd0 R)) (Finset.mem_univ Q)
      rw [hz] at hav
      have hprod : (ambientMass Q : ℝ) * (conditionalDistance (d := d) β Q : ℝ) = 0 := by
        nlinarith [mul_nonneg (hw Q).le (hd0 Q)]
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hw Q))
    simp [mass, badZoom, hz, hzero]
  · have hep : 0 < zoomError β J := lt_of_le_of_ne he (Ne.symm hz)
    have hpoint (Q : Advice J a) :
        (if badZoom (d := d) β Q then (ambientMass Q : ℝ) else 0) *
          (zoomError β J * (2 : ℝ)^(d+5)) ≤
            (ambientMass Q : ℝ) * (conditionalDistance (d := d) β Q : ℝ) := by
      by_cases hb : zoomError β J * (2 : ℝ)^(d+5) < (conditionalDistance (d := d) β Q : ℝ)
      · simp only [badZoom, hb, decide_true, Bool.true_eq, ite_true]
        exact mul_le_mul_of_nonneg_left hb.le (hw Q).le
      · simp [badZoom, hb, mul_nonneg (hw Q).le (hd0 Q)]
    have hs := Finset.sum_le_sum (fun Q (_ : Q ∈ (Finset.univ : Finset (Advice J a))) => hpoint Q)
    rw [← Finset.sum_mul] at hs
    have hm : (mass (ambientMass : Advice J a → ℚ) (badZoom (d := d) β) : ℝ) =
        ∑ Q : Advice J a, if badZoom (d := d) β Q then (ambientMass Q : ℝ) else 0 := by
      simp only [mass, Rat.cast_sum, apply_ite, Rat.cast_zero]
    rw [← hm] at hs
    have hbound := hs.trans hav
    have hpos : 0 < zoomError β J * (2 : ℝ)^(d+5) := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [hbound]

theorem goodZoom_distance_le (β : ℚ) (Q : Advice J a)
    (hQ : badZoom (d := d) β Q = false) :
    (conditionalDistance (d := d) β Q : ℝ) ≤ zoomError β J * (2 : ℝ)^(d+5) := by
  by_contra h
  have ht := lt_of_not_ge h
  simp [badZoom, ht] at hQ

/-- The source's small-beta hypothesis implies positive containment events. -/
lemma beta_lt_one_of_source (β : ℚ) (hβ : 0 ≤ β) (d : ℕ)
    (hsmall : (2 : ℚ)^d * β ≤ 1/8) : β < 1 := by
  have hp : (1 : ℚ) ≤ 2^d := one_le_pow₀ (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hp hβ]

/-- KMS 4.7, with an explicit actual exceptional set and actual conditional
samplers. The advertised square-root/fourth-root constants are unchanged. -/
theorem actual_conditioned_covering (β : ℚ) (hβ : 0 ≤ β)
    (had : a < d) (hdJ : d ≤ J) (hsmall : (2 : ℚ)^d * β ≤ 1/8) :
    (mass (ambientMass : Advice J a → ℚ) (badZoom (d := d) β) : ℝ) ≤
        Real.sqrt (β : ℝ) * (J : ℝ)^(1/4 : ℝ) ∧
    ∀ Q : Advice J a, badZoom (d := d) β Q = false →
      (∑ L : Advice J d, deletedConditional β Q L) = 1 ∧
      (AdviceExceptions.tv (ambientConditional (d := d) Q) (deletedConditional β Q) : ℝ) ≤
        Real.sqrt (β : ℝ) * (J : ℝ)^(1/4 : ℝ) * (2 : ℝ)^(d+5) := by
  have hb := beta_lt_one_of_source β hβ d hsmall
  constructor
  · simpa only [zoomError_eq_source] using badZoom_mass_le β hβ hb had.le hdJ
  · intro Q hQ
    constructor
    · exact deletedConditional_normalized β hβ hb Q had.le hdJ
    · simpa only [conditionalDistance, zoomError_eq_source] using
        goodZoom_distance_le β Q hQ

end
end PvNP.RealizableHardness.ConditionedCovering
