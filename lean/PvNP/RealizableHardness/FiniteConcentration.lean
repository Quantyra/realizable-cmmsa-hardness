import PvNP.RealizableHardness.FiniteSampling
import PvNP.RealizableHardness.BernoulliMGF

/-! Concentration for the explicit finite rational product distribution. -/
namespace PvNP.RealizableHardness.FiniteConcentration
open scoped BigOperators
open FiniteSampling

noncomputable def indicator {A : Type*} (f : A → Bool) (a : A) : ℝ := if f a then 1 else 0
noncomputable def mean {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool) : ℝ :=
  ∑ a, (q a : ℝ) * indicator f a
noncomputable def centeredSum {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (M : ℕ) (x : Fin M → A) : ℝ := ∑ i, (indicator f (x i) - mean q f)
noncomputable def probability {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (event : (Fin M → A) → Prop) : ℝ := by
  classical
  exact ∑ x, if event x then (trialMass q M x : ℝ) else 0

lemma indicator_nonneg {A : Type*} (f : A → Bool) (a : A) : 0 ≤ indicator f a := by
  unfold indicator; split <;> norm_num
lemma indicator_le_one {A : Type*} (f : A → Bool) (a : A) : indicator f a ≤ 1 := by
  unfold indicator; split <;> norm_num
lemma mean_bounds {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) : 0 ≤ mean q f ∧ mean q f ≤ 1 := by
  have hn' : ∑ a, (q a : ℝ) = 1 := by exact_mod_cast hn
  constructor
  · exact Finset.sum_nonneg (fun a _ => mul_nonneg (by exact_mod_cast hq a) (indicator_nonneg f a))
  · calc
      mean q f ≤ ∑ a, (q a : ℝ) * 1 := Finset.sum_le_sum (fun a _ =>
        mul_le_mul_of_nonneg_left (indicator_le_one f a) (by exact_mod_cast hq a))
      _ = 1 := by simpa using hn'

lemma one_trial_mgf {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hn : ∑ a, q a = 1) (t : ℝ) :
    (∑ a, (q a : ℝ) * Real.exp (t * (indicator f a - mean q f))) =
      (1 - mean q f) * Real.exp (-t * mean q f) +
        mean q f * Real.exp (t * (1 - mean q f)) := by
  have hn' : ∑ a, (q a : ℝ) = 1 := by exact_mod_cast hn
  have hs : ∑ a, (q a : ℝ) * (1 - indicator f a) = 1 - mean q f := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hn', mean]
  calc
    _ = ∑ a, ((q a : ℝ) * (1 - indicator f a) * Real.exp (-t * mean q f) +
        (q a : ℝ) * indicator f a * Real.exp (t * (1 - mean q f))) := by
      apply Finset.sum_congr rfl
      intro a _
      cases h : f a <;> simp [indicator, h]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hs]; rfl

lemma exp_finite_sum {I : Type*} (s : Finset I) (g : I → ℝ) :
    Real.exp (∑ i ∈ s, g i) = ∏ i ∈ s, Real.exp (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, Real.exp_add, ih]

lemma product_mgf_identity {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (M : ℕ) (t : ℝ) :
    (∑ x, (trialMass q M x : ℝ) * Real.exp (t * centeredSum q f M x)) =
      (∑ a, (q a : ℝ) * Real.exp (t * (indicator f a - mean q f))) ^ M := by
  classical
  calc
    _ = ∑ x : Fin M → A, ∏ i, ((q (x i) : ℝ) * Real.exp (t * (indicator f (x i) - mean q f))) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [centeredSum, Finset.mul_sum, exp_finite_sum, trialMass, Rat.cast_prod, Finset.prod_mul_distrib]
    _ = ∏ _i : Fin M, ∑ a, (q a : ℝ) * Real.exp (t * (indicator f a - mean q f)) := by
      rw [Fintype.prod_sum]
    _ = _ := by simp

lemma product_mgf_bound {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (t : ℝ) :
    (∑ x, (trialMass q M x : ℝ) * Real.exp (t * centeredSum q f M x)) ≤
      Real.exp ((M : ℝ) * t ^ 2 / 8) := by
  rw [product_mgf_identity, one_trial_mgf q f hn]
  have hb := mean_bounds q f hq hn
  have h := BernoulliMGF.centered_mgf_le (mean q f) t hb.1 hb.2
  have hlo : 0 ≤ (1 - mean q f) * Real.exp (-t * mean q f) +
      mean q f * Real.exp (t * (1 - mean q f)) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hb.2) (Real.exp_pos _).le)
      (mul_nonneg hb.1 (Real.exp_pos _).le)
  calc
    _ ≤ (Real.exp (t ^ 2 / 8)) ^ M := pow_le_pow_left₀ hlo h M
    _ = Real.exp ((M : ℝ) * t ^ 2 / 8) := by rw [← Real.exp_nat_mul]; congr 1; ring


lemma probability_mono {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (hq : ∀ a, 0 ≤ q a) (E F : (Fin M → A) → Prop) (h : ∀ x, E x → F x) :
    probability q M E ≤ probability q M F := by
  classical
  apply Finset.sum_le_sum
  intro x _
  have hx : (0 : ℝ) ≤ trialMass q M x := by exact_mod_cast trialMass_nonneg q M hq x
  by_cases he : E x
  · simp [he, h x he]
  · simp [he]; split <;> first | exact hx | exact le_rfl

lemma exponential_markov {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (t a : ℝ) :
    probability q M (fun x => a ≤ t * centeredSum q f M x) ≤
      Real.exp ((M : ℝ) * t ^ 2 / 8 - a) := by
  classical
  have hsum : probability q M (fun x => a ≤ t * centeredSum q f M x) * Real.exp a ≤
      ∑ x, (trialMass q M x : ℝ) * Real.exp (t * centeredSum q f M x) := by
    unfold probability
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    have hx : (0 : ℝ) ≤ trialMass q M x := by exact_mod_cast trialMass_nonneg q M hq x
    split_ifs with he
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hx
    · simpa using mul_nonneg hx (Real.exp_pos _).le
  have h := hsum.trans (product_mgf_bound q f hq hn M t)
  apply (le_div_iff₀ (Real.exp_pos a)).mpr at h
  simpa [Real.exp_sub] using h

lemma upper_tail {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    probability q M (fun x => (M : ℝ) * δ ≤ centeredSum q f M x) ≤
      Real.exp (-2 * (M : ℝ) * δ ^ 2) := by
  have hm := probability_mono q M hq
    (fun x => (M : ℝ) * δ ≤ centeredSum q f M x)
    (fun x => 4 * (M : ℝ) * δ ^ 2 ≤ (4 * δ) * centeredSum q f M x)
    (fun x hx => by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx)])
  have he := exponential_markov q f hq hn M (4 * δ) (4 * (M : ℝ) * δ ^ 2)
  have hid : (M : ℝ) * (4 * δ) ^ 2 / 8 - 4 * (M : ℝ) * δ ^ 2 = -2 * (M : ℝ) * δ ^ 2 := by ring
  rw [hid] at he
  exact hm.trans he

lemma lower_tail {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    probability q M (fun x => centeredSum q f M x ≤ -(M : ℝ) * δ) ≤
      Real.exp (-2 * (M : ℝ) * δ ^ 2) := by
  have hm := probability_mono q M hq
    (fun x => centeredSum q f M x ≤ -(M : ℝ) * δ)
    (fun x => 4 * (M : ℝ) * δ ^ 2 ≤ (-4 * δ) * centeredSum q f M x)
    (fun x hx => by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx)])
  have he := exponential_markov q f hq hn M (-4 * δ) (4 * (M : ℝ) * δ ^ 2)
  have hid : (M : ℝ) * (-4 * δ) ^ 2 / 8 - 4 * (M : ℝ) * δ ^ 2 = -2 * (M : ℝ) * δ ^ 2 := by ring
  rw [hid] at he
  exact hm.trans he

lemma probability_union {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (hq : ∀ a, 0 ≤ q a) (E F : (Fin M → A) → Prop) :
    probability q M (fun x => E x ∨ F x) ≤ probability q M E + probability q M F := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf, trialMass_nonneg q M hq x]

/-- Exact two-sided exponent-two Hoeffding bound for the actual finite product law. -/
theorem two_sided_tail {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    probability q M (fun x => (M : ℝ) * δ ≤ |centeredSum q f M x|) ≤
      2 * Real.exp (-2 * (M : ℝ) * δ ^ 2) := by
  have hm := probability_mono q M hq
    (fun x => (M : ℝ) * δ ≤ |centeredSum q f M x|)
    (fun x => (M : ℝ) * δ ≤ centeredSum q f M x ∨ centeredSum q f M x ≤ -(M : ℝ) * δ)
    (fun x hx => by rcases le_abs.mp hx with h | h; exact Or.inl h; exact Or.inr (by linarith only [h]))
  have hu := probability_union q M hq
    (fun x => (M : ℝ) * δ ≤ centeredSum q f M x)
    (fun x => centeredSum q f M x ≤ -(M : ℝ) * δ)
  have h1 := upper_tail q f hq hn M δ hδ
  have h2 := lower_tail q f hq hn M δ hδ
  linarith

lemma probability_exists {A B : Type*} [Fintype A] [Fintype B] (q : A → ℚ) (M : ℕ)
    (hq : ∀ a, 0 ≤ q a) (E : B → (Fin M → A) → Prop) :
    probability q M (fun x => ∃ b, E b x) ≤ ∑ b, probability q M (E b) := by
  classical
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hx : (0 : ℝ) ≤ trialMass q M x := by exact_mod_cast trialMass_nonneg q M hq x
  have hnon : ∀ b : B, 0 ≤ (if E b x then (trialMass q M x : ℝ) else 0) := by
    intro b; split <;> first | exact hx | exact le_rfl
  by_cases he : ∃ b, E b x
  · rw [if_pos he]
    obtain ⟨b, hb⟩ := he
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hnon j) (Finset.mem_univ b)
    simpa [hb] using h
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun b _ => hnon b)

noncomputable def empirical {A : Type*} (f : A → Bool) (M : ℕ) (x : Fin M → A) : ℝ :=
  (∑ i, indicator f (x i)) / M

lemma centered_empirical {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (M : ℕ) (hM : 0 < M) (x : Fin M → A) :
    centeredSum q f M x = (M : ℝ) * (empirical f M x - mean q f) := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [centeredSum, empirical, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp


lemma empirical_tail {A : Type*} [Fintype A] (q : A → ℚ) (f : A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (hM : 0 < M)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    probability q M (fun x => δ ≤ |empirical f M x - mean q f|) ≤
      2 * Real.exp (-2 * (M : ℝ) * δ ^ 2) := by
  apply (probability_mono q M hq _ _ ?_).trans (two_sided_tail q f hq hn M δ hδ)
  intro x hx
  rw [centered_empirical q f M hM x, abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
  exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg M)

/-- Simultaneous empirical failure over exactly all 2^N Boolean assignments. -/
theorem assignment_empirical_tail {A : Type*} [Fintype A] (q : A → ℚ)
    (N : ℕ) (f : (Fin N → Bool) → A → Bool)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (hM : 0 < M)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    probability q M (fun x => ∃ b : Fin N → Bool, δ ≤ |empirical (f b) M x - mean q (f b)|) ≤
      (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * δ ^ 2)) := by
  apply (probability_exists q M hq _).trans
  calc
    _ ≤ ∑ _b : Fin N → Bool, 2 * Real.exp (-2 * (M : ℝ) * δ ^ 2) :=
      Finset.sum_le_sum (fun b _ => empirical_tail q (f b) hq hn M hM δ hδ)
    _ = _ := by simp [Fintype.card_fun]

/-- A deterministic distributional approximation error composes with actual concentration. -/
theorem assignment_approximation_tail {A : Type*} [Fintype A] (q : A → ℚ)
    (N : ℕ) (f : (Fin N → Bool) → A → Bool) (μ : (Fin N → Bool) → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (hM : 0 < M)
    (δ : ℝ) (hδ : 0 ≤ δ) (happrox : ∀ b, |mean q (f b) - μ b| ≤ δ) :
    probability q M (fun x => ∃ b : Fin N → Bool, 2 * δ ≤ |empirical (f b) M x - μ b|) ≤
      (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * δ ^ 2)) := by
  apply (probability_mono q M hq _ _ ?_).trans (assignment_empirical_tail q N f hq hn M hM δ hδ)
  intro x hx
  obtain ⟨b, hb⟩ := hx
  refine ⟨b, ?_⟩
  have ht : |empirical (f b) M x - μ b| ≤
      |empirical (f b) M x - mean q (f b)| + |mean q (f b) - μ b| := abs_sub_le _ _ _
  have ha := happrox b
  linarith only [ht, ha, hb]

/-- The manuscript's eps/8 sampling error plus eps/8 distribution error gives eps/4. -/
theorem assignment_epsilon_tail {A : Type*} [Fintype A] (q : A → ℚ)
    (N : ℕ) (f : (Fin N → Bool) → A → Bool) (μ : (Fin N → Bool) → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hn : ∑ a, q a = 1) (M : ℕ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 ≤ ε) (happrox : ∀ b, |mean q (f b) - μ b| ≤ ε / 8) :
    probability q M (fun x => ∃ b : Fin N → Bool, ε / 4 ≤ |empirical (f b) M x - μ b|) ≤
      (2 ^ N : ℝ) * (2 * Real.exp (-2 * (M : ℝ) * (ε / 8) ^ 2)) := by
  have h := assignment_approximation_tail q N f μ hq hn M hM (ε / 8) (by positivity) happrox
  have he : 2 * (ε / 8) = ε / 4 := by ring
  simpa only [he] using h

lemma probability_complement {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (hn : ∑ a, q a = 1) (E : (Fin M → A) → Prop) :
    probability q M (fun x => ¬ E x) = 1 - probability q M E := by
  classical
  have hs : probability q M (fun x => ¬ E x) + probability q M E = 1 := by
    unfold probability
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ x, (trialMass q M x : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases he : E x <;> simp [he]
      _ = 1 := by exact_mod_cast trialMass_sum q M hn
  linarith only [hs]

end PvNP.RealizableHardness.FiniteConcentration