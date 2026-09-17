import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Finite rational Bayes and normalized reweighting. Concrete Grassmann and
covering instantiations are not supplied by this module. -/
namespace PvNP.RealizableHardness.PosteriorReweighting
open scoped BigOperators
variable {V Q : Type*} [Fintype V] [Fintype Q]

noncomputable def marginal (p : V → ℚ) (k : V → Q → ℚ) (q : Q) : ℚ :=
  ∑ v, p v * k v q
noncomputable def posterior (p : V → ℚ) (k : V → Q → ℚ) (q : Q) (v : V) : ℚ :=
  p v * k v q / marginal p k q
noncomputable def mass (r : V → ℚ) (b : V → Bool) : ℚ :=
  ∑ v, if b v then r v else 0

lemma marginal_nonneg (p : V → ℚ) (k : V → Q → ℚ)
    (hp : ∀ v, 0 ≤ p v) (hk : ∀ v q, 0 ≤ k v q) (q : Q) :
    0 ≤ marginal p k q := Finset.sum_nonneg fun v _ => mul_nonneg (hp v) (hk v q)

lemma marginal_normalized (p : V → ℚ) (k : V → Q → ℚ)
    (hp : ∑ v, p v = 1) (hk : ∀ v, ∑ q, k v q = 1) :
    ∑ q, marginal p k q = 1 := by
  unfold marginal
  rw [Finset.sum_comm]
  simpa only [← Finset.mul_sum, hk, mul_one] using hp

lemma posterior_normalized (p : V → ℚ) (k : V → Q → ℚ) (q : Q)
    (hq : 0 < marginal p k q) : ∑ v, posterior p k q v = 1 := by
  simp only [posterior, ← Finset.sum_div]
  exact div_self (ne_of_gt hq)

lemma bayes_mass (p : V → ℚ) (k : V → Q → ℚ) (q : Q) (v : V)
    (hq : 0 < marginal p k q) :
    posterior p k q v * marginal p k q = p v * k v q := by
  exact div_mul_cancel₀ _ (ne_of_gt hq)

lemma zero_prior (p : V → ℚ) (k : V → Q → ℚ) (q : Q) (v : V)
    (hv : p v = 0) : posterior p k q v = 0 := by simp [posterior, hv]

lemma bayes_ratio (p : V → ℚ) (k : V → Q → ℚ) (q : Q) (v : V)
    (hv : 0 < p v) : posterior p k q v / p v = k v q / marginal p k q := by
  unfold posterior
  by_cases hm : marginal p k q = 0
  · simp [hm]
  · field_simp [ne_of_gt hv, hm]

lemma joint_zero_of_marginal_zero (p : V → ℚ) (k : V → Q → ℚ)
    (hp : ∀ v, 0 ≤ p v) (hk : ∀ v q, 0 ≤ k v q)
    (q : Q) (hq : marginal p k q = 0) (v : V) : p v * k v q = 0 := by
  have hle : p v * k v q ≤ marginal p k q :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hp i) (hk i q)) (Finset.mem_univ v)
  exact le_antisymm (hq ▸ hle) (mul_nonneg (hp v) (hk v q))

lemma total_probability (p : V → ℚ) (k : V → Q → ℚ)
    (hp : ∀ v, 0 ≤ p v) (hk : ∀ v q, 0 ≤ k v q)
    (hn : ∀ v, ∑ q, k v q = 1) (v : V) :
    ∑ q, posterior p k q v * marginal p k q = p v := by
  calc
    _ = ∑ q, p v * k v q := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : marginal p k q = 0
      · simp [h, joint_zero_of_marginal_zero p k hp hk q h v]
      · exact bayes_mass p k q v (lt_of_le_of_ne (marginal_nonneg p k hp hk q) (Ne.symm h))
    _ = p v := by rw [← Finset.mul_sum, hn, mul_one]

lemma posterior_event_cutoff (p : V → ℚ) (k : V → Q → ℚ)
    (hp : ∀ v, 0 ≤ p v) (hk : ∀ v q, 0 ≤ k v q)
    (q : Q) (b g : V → Bool) (C : ℚ) (hC : 0 ≤ C)
    (hgood : ∀ v, g v = true → posterior p k q v ≤ C * p v) :
    mass (posterior p k q) b ≤ C * mass p b + mass (posterior p k q) (fun v => !(g v)) := by
  unfold mass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hr : 0 ≤ posterior p k q v :=
    div_nonneg (mul_nonneg (hp v) (hk v q)) (marginal_nonneg p k hp hk q)
  cases hb : b v
  · cases hg : g v <;> simp [hb, hg, hr]
  · cases hg : g v
    · simp only [hb, hg, Bool.not_false, Bool.true_eq, ite_true]
      linarith [mul_nonneg hC (hp v)]
    · simpa [hb, hg] using hgood v hg

noncomputable def normalizer (r w : V → ℚ) : ℚ := ∑ v, r v * w v
noncomputable def mean (r a : V → ℚ) : ℚ := ∑ v, r v * a v

lemma reweight_error (r w : V → ℚ) (g : V → Bool) (p0 eta zeta : ℚ)
    (hr : ∀ v, 0 ≤ r v) (hrn : ∑ v, r v = 1)
    (hw : ∀ v, 0 ≤ w v ∧ w v ≤ 1) (hp0 : 0 < p0) (hp1 : p0 ≤ 1)
    (he : 0 ≤ eta) (hz : 0 ≤ zeta)
    (hgood : ∀ v, g v = true → |w v / p0 - 1| ≤ eta)
    (hbad : mass r (fun v => !(g v)) ≤ zeta) :
    (∑ v, r v * |w v - p0|) ≤ p0 * eta + zeta := by
  have hpoint : ∀ v, r v * |w v - p0| ≤ r v * (p0 * eta) +
      (if !(g v) then r v else 0) := by
    intro v
    cases hg : g v
    · have habs : |w v - p0| ≤ 1 := abs_le.mpr ⟨by linarith [(hw v).1], by linarith [(hw v).2]⟩
      simp only [hg, Bool.not_false, Bool.true_eq, ite_true]
      have hbound := mul_le_mul_of_nonneg_left habs (hr v)
      have hn : 0 ≤ r v * (p0 * eta) := mul_nonneg (hr v) (mul_nonneg (le_of_lt hp0) he)
      linarith
    · have hs := hgood v hg
      have hid : w v - p0 = p0 * (w v / p0 - 1) := by field_simp
      rw [hid, abs_mul, abs_of_pos hp0]
      simp only [hg, Bool.not_true, Bool.false_eq_true, ite_false, add_zero]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (le_of_lt hp0)) (hr v)
  calc
    _ ≤ ∑ v, (r v * (p0 * eta) + (if !(g v) then r v else 0)) := Finset.sum_le_sum fun v _ => hpoint v
    _ = p0 * eta + mass r (fun v => !(g v)) := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hrn]; simp [mass]
    _ ≤ p0 * eta + zeta := add_le_add le_rfl hbad

lemma normalizer_deviation (r w : V → ℚ) (p0 : ℚ)
    (hr : ∀ v, 0 ≤ r v) (hrn : ∑ v, r v = 1) :
    |normalizer r w - p0| ≤ ∑ v, r v * |w v - p0| := by
  have hid : normalizer r w - p0 = ∑ v, r v * (w v - p0) := by
    simp [normalizer, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrn]
  rw [hid]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [abs_mul, abs_of_nonneg (hr v)]


/-- Generic finite mixture comparison; stability and bad-mass inputs remain explicit. -/
theorem normalized_reweighting (r w : V → ℚ) (g : V → Bool) (p0 eta zeta : ℚ)
    (hr : ∀ v, 0 ≤ r v) (hrn : ∑ v, r v = 1)
    (hw : ∀ v, 0 ≤ w v ∧ w v ≤ 1) (hp0 : 0 < p0) (hp1 : p0 ≤ 1)
    (he : 0 ≤ eta) (hz : 0 ≤ zeta)
    (hsmall : eta + zeta / p0 ≤ 1 / 2)
    (hgood : ∀ v, g v = true → |w v / p0 - 1| ≤ eta)
    (hbad : mass r (fun v => !(g v)) ≤ zeta) :
    p0 / 2 ≤ normalizer r w ∧ 0 < normalizer r w ∧
    mass (fun v => r v * w v / normalizer r w) (fun v => !(g v)) ≤ 2 * zeta / p0 ∧
    (∀ a : V → ℚ, (∀ v, 0 ≤ a v ∧ a v ≤ 1) →
      |mean r a - (∑ v, r v * w v * a v) / normalizer r w| ≤ 4 * eta + 4 * zeta / p0) := by
  have herr := reweight_error r w g p0 eta zeta hr hrn hw hp0 hp1 he hz hgood hbad
  have hdev := (normalizer_deviation r w p0 hr hrn).trans herr
  have hsmall' : p0 * eta + zeta ≤ p0 / 2 := by
    have h := mul_le_mul_of_nonneg_left hsmall (le_of_lt hp0)
    have hc : zeta / p0 * p0 = zeta := div_mul_cancel₀ _ (ne_of_gt hp0)
    nlinarith
  have hZ : p0 / 2 ≤ normalizer r w := by have := (abs_le.mp hdev).1; linarith
  have hZpos : 0 < normalizer r w := by linarith
  refine ⟨hZ, hZpos, ?_, ?_⟩
  · have hb : mass (fun v => r v * w v) (fun v => !(g v)) ≤ zeta := by
      apply le_trans _ hbad
      unfold mass
      apply Finset.sum_le_sum
      intro v _
      split
      · exact mul_le_of_le_one_right (hr v) (hw v).2
      · rfl
    have hid : mass (fun v => r v * w v / normalizer r w) (fun v => !(g v)) =
        mass (fun v => r v * w v) (fun v => !(g v)) / normalizer r w := by
      unfold mass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      split <;> simp
    rw [hid]
    apply (div_le_iff₀ hZpos).2
    have : zeta ≤ (2 * zeta / p0) * normalizer r w := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp0).2
      nlinarith
    exact hb.trans this
  · intro a ha
    have hA0 : 0 ≤ mean r a := Finset.sum_nonneg fun v _ => mul_nonneg (hr v) (ha v).1
    have hA1 : mean r a ≤ 1 := by
      calc
        _ ≤ ∑ v, r v := Finset.sum_le_sum fun v _ => by nlinarith [hr v, (ha v).2]
        _ = 1 := hrn
    have hN : |(∑ v, r v * w v * a v) - p0 * mean r a| ≤ p0 * eta + zeta := by
      have hid : (∑ v, r v * w v * a v) - p0 * mean r a =
          ∑ v, (r v * (w v - p0)) * a v := by
        simp only [mean, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [hid]
      apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ herr)
      apply Finset.sum_le_sum
      intro v _
      rw [abs_mul, abs_mul, abs_of_nonneg (hr v), abs_of_nonneg (ha v).1]
      exact mul_le_of_le_one_right (mul_nonneg (hr v) (abs_nonneg _)) (ha v).2
    have hnum : |mean r a * normalizer r w - ∑ v, r v * w v * a v| ≤ 2 * (p0 * eta + zeta) := by
      have hid : mean r a * normalizer r w - ∑ v, r v * w v * a v =
          mean r a * (normalizer r w - p0) - ((∑ v, r v * w v * a v) - p0 * mean r a) := by ring
      rw [hid]
      apply (abs_sub _ _).trans
      rw [abs_mul, abs_of_nonneg hA0]
      have hm : mean r a * |normalizer r w - p0| ≤ p0 * eta + zeta :=
        (mul_le_of_le_one_left (abs_nonneg _) hA1).trans hdev
      linarith
    have hid : mean r a - (∑ v, r v * w v * a v) / normalizer r w =
        (mean r a * normalizer r w - ∑ v, r v * w v * a v) / normalizer r w := by field_simp
    rw [hid, abs_div, abs_of_pos hZpos]
    apply (div_le_iff₀ hZpos).2
    have hc : 0 ≤ 4 * eta + 4 * zeta / p0 := by positivity
    have hm := mul_le_mul_of_nonneg_left hZ hc
    have heq : (4 * eta + 4 * zeta / p0) * (p0 / 2) = 2 * (p0 * eta + zeta) := by field_simp; ring
    rw [heq] at hm
    exact hnum.trans hm

lemma reweighted_normalized (r w : V → ℚ) (hZ : 0 < normalizer r w) :
    ∑ v, r v * w v / normalizer r w = 1 := by
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

end PvNP.RealizableHardness.PosteriorReweighting
