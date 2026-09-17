import PvNP.RealizableHardness.JointSamplingLaw
import PvNP.RealizableHardness.SamplingThreshold

/-! Actual bit-array guarantees relative to the original rational law. No encoded runtime claim. -/
namespace PvNP.RealizableHardness.SamplingGuarantee
open scoped BigOperators
open FiniteSampling JointSamplingLaw FiniteConcentration

def roundedLaw (p : ℕ → ℚ) (S b : ℕ) (i : Fin S) : ℚ := mass p (2 ^ b) i.val

noncomputable def originalMean (p : ℕ → ℚ) (S : ℕ) (f : ℕ → Bool) : ℝ :=
  (eventMass p S f : ℝ)

lemma finiteMean_eq_eventMass (p : ℕ → ℚ) (S : ℕ) (f : ℕ → Bool) :
    mean (fun i : Fin S => p i.val) (fun i => f i.val) = (eventMass p S f : ℝ) := by
  unfold mean indicator eventMass
  rw [← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i.val = true <;> simp [h]

lemma roundedLaw_nonneg (p : ℕ → ℚ) (S b : ℕ) (hp : ∀ i, 0 ≤ p i) :
    ∀ i, 0 ≤ roundedLaw p S b i := fun i => mass_nonneg p (2 ^ b) hp i.val

lemma roundedLaw_sum (p : ℕ → ℚ) (S b : ℕ) (hn : cumulative p S = 1) :
    ∑ i, roundedLaw p S b i = 1 := by
  unfold roundedLaw
  rw [Fin.sum_univ_eq_sum_range]
  exact mass_sum p (2 ^ b) S (by positivity) hn

lemma roundedMean_error (p : ℕ → ℚ) (S b : ℕ) (eps : ℚ)
    (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ)) (f : ℕ → Bool) :
    |mean (roundedLaw p S b) (fun i => f i.val) - originalMean p S f| ≤ (eps : ℝ) / 8 := by
  change |mean (fun i : Fin S => mass p (2 ^ b) i.val) (fun i => f i.val) -
    (eventMass p S f : ℝ)| ≤ (eps : ℝ) / 8
  rw [finiteMean_eq_eventMass]
  exact_mod_cast event_error_of_precision p S b eps hp heps hgrid f

noncomputable def Good (p : ℕ → ℚ) (S N M : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ) (draws : Fin M → Fin S) : Prop :=
  ∀ x, |empirical (fun i : Fin S => F x i.val) M draws - originalMean p S (F x)| < (eps : ℝ) / 4

/-- Concentration is transported to actual independent bit blocks and original-law means. -/
theorem seed_failure_bound (p : ℕ → ℚ) (S b N M : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps) (hM : 0 < M)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ)) :
    seedProbability M b (fun seeds => ¬ Good p S N M F eps (sampleArray p S b M hn seeds)) ≤
      (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * ((eps : ℝ) / 8) ^ 2)) := by
  rw [sampleArray_probability p S b M hn hp (fun draws => ¬ Good p S N M F eps draws)]
  have h := assignment_epsilon_tail (roundedLaw p S b) N
    (fun x (i : Fin S) => F x i.val) (fun x => originalMean p S (F x))
    (roundedLaw_nonneg p S b hp) (roundedLaw_sum p S b hn) M hM (eps : ℝ)
    (by exact_mod_cast heps.le) (fun x => roundedMean_error p S b eps hp heps hgrid (F x))
  change probability (roundedLaw p S b) M (fun draws => ¬ Good p S N M F eps draws) ≤ _
  simpa only [Good, not_forall, not_lt] using h

theorem seed_success_bound (p : ℕ → ℚ) (S b N M : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps) (hM : 0 < M)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ)) :
    1 - (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * ((eps : ℝ) / 8) ^ 2)) ≤
      seedProbability M b (fun seeds => Good p S N M F eps (sampleArray p S b M hn seeds)) := by
  have hf := seed_failure_bound p S b N M F eps hn hp heps hM hgrid
  rw [sampleArray_probability p S b M hn hp (fun draws => ¬ Good p S N M F eps draws)] at hf
  rw [sampleArray_probability p S b M hn hp (Good p S N M F eps)]
  have hc := probability_complement (roundedLaw p S b) M (roundedLaw_sum p S b hn)
    (Good p S N M F eps)
  change probability (roundedLaw p S b) M (fun x => ¬ Good p S N M F eps x) ≤ _ at hf
  rw [hc] at hf
  change _ ≤ probability (roundedLaw p S b) M (Good p S N M F eps)
  linarith

theorem good_probability_of_threshold (p : ℕ → ℚ) (S b N M : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ))
    (hM : SamplingThreshold.threshold N (eps : ℝ) ≤ (M : ℝ)) :
    (2 / 3 : ℝ) ≤ seedProbability M b
      (fun seeds => Good p S N M F eps (sampleArray p S b M hn seeds)) := by
  have hepsR : (0 : ℝ) < eps := by exact_mod_cast heps
  have hMpos : 0 < M := by
    have h := lt_of_lt_of_le (SamplingThreshold.threshold_pos N eps hepsR) hM
    exact_mod_cast h
  have hs := seed_success_bound p S b N M F eps hn hp heps hMpos hgrid
  have hf := SamplingThreshold.failure_budget N M eps hepsR hM
  linarith

theorem good_probability_of_learningThreshold (p : ℕ → ℚ) (S b N M : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ))
    (hM : SamplingThreshold.learningThreshold N (eps : ℝ) ≤ (M : ℝ)) :
    (5 / 6 : ℝ) ≤ seedProbability M b
      (fun seeds => Good p S N M F eps (sampleArray p S b M hn seeds)) := by
  have hepsR : (0 : ℝ) < eps := by exact_mod_cast heps
  have hMpos : 0 < M := by
    have h := lt_of_lt_of_le (SamplingThreshold.threshold_pos N eps hepsR)
      ((SamplingThreshold.threshold_le_learningThreshold N eps).trans hM)
    exact_mod_cast h
  have hs := seed_success_bound p S b N M F eps hn hp heps hMpos hgrid
  have hf := SamplingThreshold.learning_failure_budget N M eps hepsR hM
  linarith

/-- A concrete rational precision choice, with dyadic grid meeting the actual atom-error bound. -/
def precision (S : ℕ) (eps : ℚ) : ℕ := Nat.clog 2 ⌈8 * (S : ℚ) / eps⌉₊

theorem precision_bound (S : ℕ) (eps : ℚ) :
    8 * (S : ℚ) / eps ≤ ((2 ^ precision S eps : ℕ) : ℚ) := by
  unfold precision
  apply (Nat.le_ceil _).trans
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) ⌈8 * (S : ℚ) / eps⌉₊

theorem chosen_good_probability (p : ℕ → ℚ) (S N : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps) :
    let b := precision S eps
    let M := SamplingThreshold.sampleCount N (eps : ℝ)
    (2 / 3 : ℝ) ≤ seedProbability M b
      (fun seeds => Good p S N M F eps (sampleArray p S b M hn seeds)) := by
  dsimp only
  exact good_probability_of_threshold p S (precision S eps) N _ F eps hn hp heps
    (precision_bound S eps) (SamplingThreshold.sampleCount_lower N eps)

theorem chosen_learning_good_probability (p : ℕ → ℚ) (S N : ℕ)
    (F : (Fin N → Bool) → ℕ → Bool) (eps : ℚ)
    (hn : cumulative p S = 1) (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps) :
    let b := precision S eps
    let M := SamplingThreshold.learningSampleCount N (eps : ℝ)
    (5 / 6 : ℝ) ≤ seedProbability M b
      (fun seeds => Good p S N M F eps (sampleArray p S b M hn seeds)) := by
  dsimp only
  exact good_probability_of_learningThreshold p S (precision S eps) N _ F eps hn hp heps
    (precision_bound S eps) (SamplingThreshold.learningSampleCount_lower N eps)

end PvNP.RealizableHardness.SamplingGuarantee
