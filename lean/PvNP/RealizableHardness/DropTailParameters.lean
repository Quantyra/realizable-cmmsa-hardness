/- UNCOMPILED source draft. No compiler or independent acceptance yet. -/
import PvNP.RealizableHardness.DropCountTail
import Mathlib.Data.Real.Archimedean

/-! Exact numerical specialization of the actual deletion tail. A is fixed before h.
The explicit sufficient threshold is intentionally generous. No double-exponential
ambient dimension, beta-range construction, or full fixed-L assembly is claimed. -/
namespace PvNP.RealizableHardness.DropTailParameters

noncomputable section

/-- Exact natural-exponent reading of the manuscript's `2^(-k h²)`. -/
def decay (k h : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k * h ^ 2)

lemma decay_eq_reciprocal (k h : ℕ) :
    decay k h = 1 / (2 : ℝ) ^ (k * h ^ 2) := by
  simp [decay, one_div, inv_pow]

lemma decay_pos (k h : ℕ) : 0 < decay k h := by
  unfold decay
  positivity

lemma decay_zero (k : ℕ) : decay k 0 = 1 := by simp [decay]

lemma decay_add (k l h : ℕ) : decay (k + l) h = decay k h * decay l h := by
  simp only [decay, Nat.add_mul, pow_add]

/-- The Markov denominator is nonzero even at h=0. -/
lemma decay_ratio (h : ℕ) : decay 100 h / decay 30 h = decay 70 h := by
  have he : decay 100 h = decay 70 h * decay 30 h := by
    simpa using decay_add 70 30 h
  rw [he, mul_div_cancel_right₀ _ (ne_of_gt (decay_pos 30 h))]

/-- Two explicit numerical inequalities, not an assumed tail estimate. -/
def Ready (A : ℝ) (h : ℕ) : Prop :=
  100 ≤ h ^ 2 ∧ 2 * Real.exp 1 * A ≤ (h : ℝ) ^ 2

lemma ready_h_pos {A : ℝ} {h : ℕ} (hr : Ready A h) : 0 < h := by
  have hh := hr.1
  by_contra hz
  have : h = 0 := Nat.eq_zero_of_not_pos hz
  subst h
  norm_num at hh

/-- Fixed A is chosen first; a single natural lower bound works for every later h. -/
theorem eventually_ready (A : ℝ) : ∃ N : ℕ, ∀ h : ℕ, N ≤ h → Ready A h := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (100 : ℝ) (2 * Real.exp 1 * A))
  refine ⟨N, ?_⟩
  intro h hNh
  have hcast : (N : ℝ) ≤ h := by exact_mod_cast hNh
  have h100 : (100 : ℝ) < h := lt_of_lt_of_le
    (lt_of_le_of_lt (le_max_left _ _) hN) hcast
  have hA : 2 * Real.exp 1 * A < (h : ℝ) := lt_of_lt_of_le
    (lt_of_le_of_lt (le_max_right _ _) hN) hcast
  have hs : (h : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, hA.le.trans hs⟩
  have : (100 : ℝ) ≤ (h : ℝ) ^ 2 := h100.le.trans hs
  exact_mod_cast this

lemma mean_le_cutoff {A : ℝ} (hA : 0 ≤ A) {h : ℕ} (hr : Ready A h) :
    A * (h : ℝ) ^ 2 ≤ ((h ^ 4 : ℕ) : ℝ) := by
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hea : A ≤ 2 * Real.exp 1 * A := by nlinarith
  have ha : A ≤ (h : ℝ) ^ 2 := hea.trans hr.2
  have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg (h : ℝ))
  push_cast
  nlinarith only [hm]

/-- At the explicit threshold, the Chernoff base is at most one half. -/
lemma chernoff_base_le_half {A : ℝ} {h : ℕ} (hr : Ready A h) :
    Real.exp 1 * A / (h : ℝ) ^ 2 ≤ 1 / 2 := by
  have hp : 0 < (h : ℝ) ^ 2 := pow_pos (by exact_mod_cast ready_h_pos hr) 2
  apply (div_le_iff₀ hp).mpr
  nlinarith only [hr.2]

lemma cutoff_dominates {A : ℝ} {h : ℕ} (hr : Ready A h) :
    100 * h ^ 2 ≤ h ^ 4 := by
  have hm := Nat.mul_le_mul_right (h ^ 2) hr.1
  nlinarith only [hm]

/-- No logarithmic or asymptotic estimate is supplied as a premise. -/
theorem numerical_chernoff {A : ℝ} (hA : 0 ≤ A) {h : ℕ} (hr : Ready A h) :
    (Real.exp 1 * A / (h : ℝ) ^ 2) ^ (h ^ 4) ≤ decay 100 h := by
  have hn : 0 ≤ Real.exp 1 * A / (h : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (Real.exp_pos 1).le hA) (sq_nonneg _)
  exact (pow_le_pow_left₀ hn (chernoff_base_le_half hr) (h ^ 4)).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (cutoff_dominates hr))

lemma chernoff_base_rewrite (A : ℝ) {h : ℕ} (hh : 0 < h) :
    Real.exp 1 * (A * (h : ℝ) ^ 2) / ((h ^ 4 : ℕ) : ℝ) =
      Real.exp 1 * A / (h : ℝ) ^ 2 := by
  have hz : (h : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hh)
  push_cast
  field_simp [hz]
  <;> ring

/-- Actual rational deletion-event mass, cast to reals, with natural cutoff h^4. -/
theorem actual_tail {A : ℝ} (hA : 0 ≤ A) {h J : ℕ} {β : ℚ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hr : Ready A h)
    (hmean : (J : ℝ) * (β : ℝ) = A * (h : ℝ) ^ 2) :
    DropCountTail.tail β J (h ^ 4) ≤ decay 100 h := by
  have hc : (J : ℝ) * (β : ℝ) ≤ ((h ^ 4 : ℕ) : ℝ) := by
    rw [hmean]
    exact mean_le_cutoff hA hr
  have ht := DropCountTail.chernoff_tail_allow_zero β hβ hβ1 J (h ^ 4) hc
  rw [hmean, chernoff_base_rewrite A (ready_h_pos hr)] at ht
  exact ht.trans (numerical_chernoff hA hr)

/-- Exact exponent subtraction used by the exceptional-advice Markov estimate. -/
theorem actual_tail_over_zeta {A : ℝ} (hA : 0 ≤ A) {h J : ℕ} {β : ℚ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hr : Ready A h)
    (hmean : (J : ℝ) * (β : ℝ) = A * (h : ℝ) ^ 2) :
    DropCountTail.tail β J (h ^ 4) / decay 30 h ≤ decay 70 h := by
  calc
    _ ≤ decay 100 h / decay 30 h :=
      div_le_div_of_nonneg_right (actual_tail hA hβ hβ1 hr hmean) (decay_pos 30 h).le
    _ = _ := decay_ratio h

/-- The uniform eventual statement quantifies over J and beta after fixing A and h. -/
theorem eventual_actual_tail (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h →
      A * (h : ℝ) ^ 2 ≤ ((h ^ 4 : ℕ) : ℝ) ∧
      (Real.exp 1 * A / (h : ℝ) ^ 2) ^ (h ^ 4) ≤ decay 100 h ∧
      ∀ (J : ℕ) (β : ℚ), 0 ≤ β → β ≤ 1 →
        (J : ℝ) * (β : ℝ) = A * (h : ℝ) ^ 2 →
        DropCountTail.tail β J (h ^ 4) ≤ decay 100 h ∧
        DropCountTail.tail β J (h ^ 4) / decay 30 h ≤ decay 70 h := by
  obtain ⟨N, hN⟩ := eventually_ready A
  refine ⟨N, ?_⟩
  intro h hh
  have hr := hN h hh
  refine ⟨mean_le_cutoff hA.le hr, numerical_chernoff hA.le hr, ?_⟩
  intro J β hb hb1 hm
  exact ⟨actual_tail hA.le hb hb1 hr hm, actual_tail_over_zeta hA.le hb hb1 hr hm⟩

end
end PvNP.RealizableHardness.DropTailParameters
