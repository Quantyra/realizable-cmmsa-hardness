/- UNCOMPILED source draft. No build or independent acceptance is claimed. -/
import PvNP.RealizableHardness.PosteriorDensity
import PvNP.RealizableHardness.DropCountTail

/-! Actual exceptional advice sets. The statistical-distance proximity estimate
itself is deliberately not supplied here. No conditional independence is used. -/
namespace PvNP.RealizableHardness.AdviceExceptions
open scoped BigOperators
open TripleRestrictionRank TripleRestrictionDimension GrassmannIncidence PosteriorDensity
open PosteriorReweighting (mass)

noncomputable section
attribute [local instance] Classical.propDecidable
variable {J a : ℕ}

/-- Standard finite total variation: half the L1 distance. -/
def tv {A : Type*} [Fintype A] (p q : A → ℚ) : ℚ :=
  (∑ x, |p x - q x|) / 2

lemma tv_nonneg {A : Type*} [Fintype A] (p q : A → ℚ) : 0 ≤ tv p q := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _) (by norm_num)

lemma tv_self {A : Type*} [Fintype A] (p : A → ℚ) : tv p p = 0 := by
  simp [tv]

/-- Sharp event bound, derived from normalization and half-L1, not a premise. -/
theorem event_sub_le_tv {A : Type*} [Fintype A] (p q : A → ℚ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (b : A → Bool) :
    mass p b - mass q b ≤ tv p q := by
  have hpoint (x : A) :
      2 * ((if b x then p x else 0) - (if b x then q x else 0)) ≤
        |p x - q x| + (p x - q x) := by
    cases hb : b x
    · simp only [hb, Bool.false_eq_true, ite_false, sub_self, mul_zero]
      have h := neg_abs_le (p x - q x)
      linarith
    · simp only [hb, Bool.true_eq, ite_true]
      have h := le_abs_self (p x - q x)
      linarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  have hz' : (∑ x, p x) - ∑ x, q x = 0 := by rw [hp, hq, sub_self]
  rw [hz'] at hs
  unfold mass tv
  linarith

lemma mass_union_le {A : Type*} [Fintype A] (p : A → ℚ)
    (hp : ∀ x, 0 ≤ p x) (b c : A → Bool) :
    mass p (fun x => b x || c x) ≤ mass p b + mass p c := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  cases hb : b x <;> cases hc : c x <;> simp [hb, hc, hp x]

/-- Actual unconditional strict-cutoff probability, kept rational for exact Bayes. -/
def priorTail (β : ℚ) (J T : ℕ) : ℚ :=
  mass (prior β : Draw J → ℚ) (fun d => decide (T < dropCount d))

lemma priorTail_cast (β : ℚ) (J T : ℕ) :
    (priorTail β J T : ℝ) = DropCountTail.tail β J T := by
  unfold priorTail mass DropCountTail.tail TripleRestrictionRank.probability
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : T < dropCount d <;> simp [hd, prior]

lemma conditional_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (Q : Advice J a) (d : Draw J) : 0 ≤ conditional β Q d := by
  exact div_nonneg (joint_nonneg β hβ hβ1 d Q)
    (adviceMarginal_nonneg β hβ hβ1 Q)

/-- Lean's zero-denominator convention contributes no exceptional null atom. -/
lemma conditional_zero_marginal (β : ℚ) (Q : Advice J a)
    (hQ : adviceMarginal β Q = 0) (d : Draw J) : conditional β Q d = 0 := by
  change prior β d * kernel d Q / adviceMarginal β Q = 0
  rw [hQ, div_zero]

lemma tailMass_zero_marginal (β : ℚ) (Q : Advice J a) (T : ℕ)
    (hQ : adviceMarginal β Q = 0) : tailMass β Q T = 0 := by
  unfold tailMass mass
  simp only [conditional_zero_marginal β Q hQ, ite_self, Finset.sum_const_zero]

lemma tailMass_nonneg (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (Q : Advice J a) (T : ℕ) : 0 ≤ tailMass β Q T := by
  unfold tailMass mass
  apply Finset.sum_nonneg
  intro d _
  split
  · exact conditional_nonneg β hβ hβ1 Q d
  · exact le_rfl

/-- Averaging the actual posterior tail recovers the original product-law tail.
The imported total-probability proof explicitly handles zero marginals. -/
theorem posterior_tail_expectation (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) (T : ℕ) :
    (∑ Q : Advice J a, adviceMarginal β Q * tailMass β Q T) = priorTail β J T := by
  unfold tailMass priorTail mass
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : T < dropCount d
  · simp only [hd, decide_true, Bool.true_eq, ite_true]
    simpa only [conditional, adviceMarginal, mul_comm] using
      PosteriorReweighting.total_probability (prior β) kernel
        (drawMass_nonneg β hβ hβ1) kernel_nonneg
        (fun d => kernel_normalized d ha) d
  · simp [hd]

def badTail (β ζ : ℚ) (T : ℕ) (Q : Advice J a) : Bool :=
  decide (ζ < tailMass β Q T)

def lowMarginal (β : ℚ) (Q : Advice J a) : Bool :=
  decide (adviceMarginal β Q < ambientMass Q / 2)

def exceptional (β ζ : ℚ) (T : ℕ) (Q : Advice J a) : Bool :=
  lowMarginal β Q || badTail β ζ T Q

def adviceTV (β : ℚ) (J a : ℕ) : ℚ :=
  tv (ambientMass : Advice J a → ℚ) (adviceMarginal β)

lemma null_marginal_not_badTail (β ζ : ℚ) (hζ : 0 < ζ) (T : ℕ)
    (Q : Advice J a) (hQ : adviceMarginal β Q = 0) : badTail β ζ T Q = false := by
  simp [badTail, tailMass_zero_marginal β Q T hQ, not_lt.mpr (le_of_lt hζ)]

/-- Markov's inequality for the actual posterior-tail random variable. -/
theorem badTail_marginal_mass_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) (T : ℕ) (ζ : ℚ) (hζ : 0 < ζ) :
    mass (adviceMarginal β : Advice J a → ℚ) (badTail β ζ T) ≤ priorTail β J T / ζ := by
  apply (le_div_iff₀ hζ).mpr
  have hpoint (Q : Advice J a) :
      (if badTail β ζ T Q then adviceMarginal β Q else 0) * ζ ≤
        adviceMarginal β Q * tailMass β Q T := by
    have hm := adviceMarginal_nonneg β hβ hβ1 Q
    by_cases hb : ζ < tailMass β Q T
    · simp only [badTail, hb, decide_true, Bool.true_eq, ite_true]
      exact mul_le_mul_of_nonneg_left (le_of_lt hb) hm
    · simp only [badTail, hb, decide_false, Bool.false_eq_true, ite_false, zero_mul]
      exact mul_nonneg hm (tailMass_nonneg β hβ hβ1 Q T)
  calc
    _ = ∑ Q : Advice J a,
        (if badTail β ζ T Q then adviceMarginal β Q else 0) * ζ := by
      rw [mass, Finset.sum_mul]
    _ ≤ ∑ Q : Advice J a, adviceMarginal β Q * tailMass β Q T :=
      Finset.sum_le_sum fun Q _ => hpoint Q
    _ = priorTail β J T := posterior_tail_expectation β hβ hβ1 ha T

theorem ambient_event_transfer (β : ℚ) (ha : a ≤ J) (b : Advice J a → Bool) :
    mass ambientMass b ≤ mass (adviceMarginal β) b + adviceTV β J a := by
  have h := event_sub_le_tv ambientMass (adviceMarginal β)
    (ambientMass_normalized ha) (adviceMarginal_normalized β ha) b
  change mass ambientMass b - mass (adviceMarginal β) b ≤ adviceTV β J a at h
  linarith

/-- Losing at least half the uniform atom costs at most twice total variation. -/
theorem lowMarginal_ambient_mass_le (β : ℚ) (ha : a ≤ J) :
    mass (ambientMass : Advice J a → ℚ) (lowMarginal β) ≤ 2 * adviceTV β J a := by
  have hs : mass (ambientMass : Advice J a → ℚ) (lowMarginal β) ≤
      2 * (mass (ambientMass : Advice J a → ℚ) (lowMarginal β) -
        mass (adviceMarginal β : Advice J a → ℚ) (lowMarginal β)) := by
    unfold mass
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Q _
    by_cases h : adviceMarginal β Q < ambientMass Q / 2
    · simp only [lowMarginal, h, decide_true, Bool.true_eq, ite_true]
      linarith
    · simp [lowMarginal, h]
  have he := event_sub_le_tv (ambientMass : Advice J a → ℚ) (adviceMarginal β)
    (ambientMass_normalized ha) (adviceMarginal_normalized β ha) (lowMarginal β)
  change mass ambientMass (lowMarginal β) - mass (adviceMarginal β) (lowMarginal β) ≤
    adviceTV β J a at he
  linarith

theorem badTail_ambient_mass_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) (T : ℕ) (ζ : ℚ) (hζ : 0 < ζ) :
    mass (ambientMass : Advice J a → ℚ) (badTail β ζ T) ≤
      priorTail β J T / ζ + adviceTV β J a := by
  exact (ambient_event_transfer β ha _).trans
    (add_le_add (badTail_marginal_mass_le β hβ hβ1 ha T ζ hζ)
      (le_refl (adviceTV β J a)))

/-- The manuscript's complete exceptional-advice union bound for the actual laws.
Only beta's probability range, a<=J and positive cutoff level are hypotheses. -/
theorem exceptional_ambient_mass_le (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) (T : ℕ) (ζ : ℚ) (hζ : 0 < ζ) :
    mass (ambientMass : Advice J a → ℚ) (exceptional β ζ T) ≤
      priorTail β J T / ζ + 3 * adviceTV β J a := by
  have hu := mass_union_le (ambientMass : Advice J a → ℚ)
    (fun Q => le_of_lt (ambientMass_pos Q ha)) (lowMarginal β) (badTail β ζ T)
  have hl := lowMarginal_ambient_mass_le β ha
  have ht := badTail_ambient_mass_le β hβ hβ1 ha T ζ hζ
  change mass ambientMass (exceptional β ζ T) ≤
    mass ambientMass (lowMarginal β) + mass ambientMass (badTail β ζ T) at hu
  linarith

theorem good_advice_properties (β ζ : ℚ) (T : ℕ) (Q : Advice J a)
    (hQ : exceptional β ζ T Q = false) :
    ambientMass Q / 2 ≤ adviceMarginal β Q ∧ tailMass β Q T ≤ ζ := by
  constructor
  · by_contra h
    have hh : adviceMarginal β Q < ambientMass Q / 2 := lt_of_not_ge h
    simp [exceptional, lowMarginal, hh] at hQ
  · by_contra h
    have hh : ζ < tailMass β Q T := lt_of_not_ge h
    simp [exceptional, badTail, hh] at hQ

/-- Real form suitable for substituting the actual Chernoff estimate. -/
theorem exceptional_ambient_mass_le_real (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) (T : ℕ) (ζ : ℚ) (hζ : 0 < ζ) :
    (mass (ambientMass : Advice J a → ℚ) (exceptional β ζ T) : ℝ) ≤
      DropCountTail.tail β J T / (ζ : ℝ) + 3 * (adviceTV β J a : ℝ) := by
  rw [← priorTail_cast]
  exact_mod_cast exceptional_ambient_mass_le β hβ hβ1 ha T ζ hζ

/-- Substitution of the actual product-law Chernoff theorem; TV proximity is
still the one undisclosed quantitative term, not a supplied event bound. -/
theorem exceptional_chernoff_bound (β : ℚ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ J) (T : ℕ) (ζ : ℚ) (hζ : 0 < ζ)
    (hT : (J : ℝ) * (β : ℝ) ≤ T) :
    (mass (ambientMass : Advice J a → ℚ) (exceptional β ζ T) : ℝ) ≤
      (Real.exp 1 * ((J : ℝ) * (β : ℝ)) / T) ^ T / (ζ : ℝ) +
        3 * (adviceTV β J a : ℝ) := by
  have hz : (0 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast (le_of_lt hζ)
  exact (exceptional_ambient_mass_le_real β hβ hβ1 ha T ζ hζ).trans
    (add_le_add (div_le_div_of_nonneg_right
      (DropCountTail.chernoff_tail_allow_zero β hβ hβ1 J T hT) hz)
      (le_refl (3 * (adviceTV β J a : ℝ))))

end
end PvNP.RealizableHardness.AdviceExceptions
