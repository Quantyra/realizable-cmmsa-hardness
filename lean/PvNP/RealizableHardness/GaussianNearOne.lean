/- UNCOMPILED source draft; no successful kernel check claimed. -/
import PvNP.RealizableHardness.GaussianRatio

namespace PvNP.RealizableHardness.GaussianNearOne
open scoped BigOperators
open GrassmannCounting GaussianRatio
noncomputable section

def leading (b c : ℕ) : ℚ := 1 / (2 : ℚ)^(b*c)
def error (m b : ℕ) : ℚ := ((2 : ℚ)^b - 1) / 2^m

lemma normalizedFrame_nonneg (h : b ≤ n) : 0 ≤ normalizedFrame n b := by
  apply Finset.prod_nonneg
  intro i hi
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)

lemma normalizedFrame_mono (hb : b ≤ m) (hm : m ≤ n) :
    normalizedFrame m b ≤ normalizedFrame n b := by
  apply Finset.prod_le_prod
  · intro i hi
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
  · intro i hi
    have hp : (2 : ℚ)^m ≤ 2^n := pow_le_pow_right₀ (by norm_num) hm
    have hd : (2 : ℚ)^i / 2^n ≤ 2^i / 2^m :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    linarith

lemma normalizedFrame_ge_one_sub_error (hb : b ≤ m) :
    1 - error m b ≤ normalizedFrame m b := by
  have hx : ∀ i ∈ Finset.range b,
      0 ≤ (2 : ℚ)^i / 2^m ∧ (2 : ℚ)^i / 2^m ≤ 1 := by
    intro i hi
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
  have hh := one_sub_sum_le_prod (Finset.range b) (fun i => (2 : ℚ)^i / 2^m) hx
  simpa [← Finset.sum_div, sum_two_pow, error, normalizedFrame] using hh

/-- Reciprocal orientation of the actual frame-count ratio; no ratio premise. -/
lemma ratio_eq_normalized (hb : b + 1 ≤ m) (hm : m ≤ n) :
    (gaussian m b : ℚ) / gaussian n b =
      leading b (n-m) * (normalizedFrame m b / normalizedFrame n b) := by
  have h := gaussian_ratio_eq (by omega : b ≤ m) hm
  have hg : (gaussian m b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (gaussian_pos (by omega : b ≤ m)))
  have hn : (gaussian n b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (gaussian_pos (by omega : b ≤ n)))
  have hfm : normalizedFrame m b ≠ 0 := by
    have := normalizedFrame_ge_half hb
    linarith
  have hfn : normalizedFrame n b ≠ 0 := by
    have := normalizedFrame_ge_half (show b + 1 ≤ n by omega)
    linarith
  have hh := congrArg (fun x : ℚ => x⁻¹) h
  simpa [leading, mul_inv_rev, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh

/-- Exact finite product of the actual binary Gaussian coefficients. -/
lemma ratio_eq_product (hc : c ≤ n) (hb : b + 1 ≤ n-c) :
    (gaussian (n-c) b : ℚ) / gaussian n b =
      leading b c *
        (∏ i ∈ Finset.range b, ((1-(2:ℚ)^i/2^(n-c)) / (1-(2:ℚ)^i/2^n))) := by
  rw [ratio_eq_normalized hb (Nat.sub_le n c), Nat.sub_sub_self hc]
  simp only [normalizedFrame, Finset.prod_div_distrib]

lemma normalized_relative_bounds (hb : b + 1 ≤ m) (hm : m ≤ n) :
    1 - error m b ≤ normalizedFrame m b / normalizedFrame n b ∧
      normalizedFrame m b / normalizedFrame n b ≤ 1 := by
  have hp : 0 < normalizedFrame n b := by
    have := normalizedFrame_ge_half (show b+1 ≤ n by omega)
    linarith
  have hm0 := normalizedFrame_nonneg (show b ≤ m by omega)
  have hn1 := normalizedFrame_le_one n b
  have hbase : normalizedFrame m b ≤ normalizedFrame m b / normalizedFrame n b := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  constructor
  · exact le_trans (normalizedFrame_ge_one_sub_error (by omega)) hbase
  · exact (div_le_one hp).mpr (normalizedFrame_mono (by omega) hm)

/-- Explicit relative error for the actual probability of an additional codimension c. -/
theorem gaussian_near_one (hc : c ≤ n) (hb : b+1 ≤ n-c) :
    leading b c * (1-error (n-c) b) ≤ (gaussian (n-c) b : ℚ) / gaussian n b ∧
      (gaussian (n-c) b : ℚ) / gaussian n b ≤ leading b c := by
  rw [ratio_eq_normalized hb (Nat.sub_le n c), Nat.sub_sub_self hc]
  have hh := normalized_relative_bounds hb (Nat.sub_le n c)
  have hp : 0 ≤ leading b c := by unfold leading; positivity
  constructor
  · exact mul_le_mul_of_nonneg_left hh.1 hp
  · simpa using mul_le_mul_of_nonneg_left hh.2 hp

lemma error_le_inverse_pow (h : b+k ≤ m) : error m b ≤ 1/(2:ℚ)^k := by
  have he : (2:ℚ)^(b+k) ≤ 2^m := pow_le_pow_right₀ (by norm_num) h
  rw [pow_add] at he
  unfold error
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [show 0 < (2:ℚ)^k by positivity]

/-- A user-chosen finite exponent, not an assumed asymptotic closeness statement. -/
theorem gaussian_near_one_pow (hc : c ≤ n) (hb : b+1 ≤ n-c)
    (hk : b+c+k ≤ n) :
    leading b c * (1-1/(2:ℚ)^k) ≤ (gaussian (n-c) b : ℚ) / gaussian n b ∧
      (gaussian (n-c) b : ℚ) / gaussian n b ≤ leading b c := by
  have hh := gaussian_near_one hc hb
  have he := error_le_inverse_pow (show b+k ≤ n-c by omega)
  have hp : 0 ≤ leading b c := by unfold leading; positivity
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left (by linarith) hp) hh.1
  · exact hh.2

theorem gaussian_probability_ge_half (hc : c ≤ n) (hb : b+1 ≤ n-c) :
    leading b c / 2 ≤ (gaussian (n-c) b : ℚ) / gaussian n b := by
  have hh := (gaussian_near_one_pow hc hb (show b+c+1 ≤ n by omega)).1
  norm_num at hh
  linarith

/-- Concrete J/2 error used in the manuscript's rank-stable posterior. -/
theorem gaussian_near_one_half_J (hc : c ≤ n) (hb : b+1 ≤ n-c)
    (hJ : b+c+J/2 ≤ n) :
    leading b c * (1-1/(2:ℚ)^(J/2)) ≤ (gaussian (n-c) b : ℚ) / gaussian n b ∧
      (gaussian (n-c) b : ℚ) / gaussian n b ≤ leading b c :=
  gaussian_near_one_pow hc hb hJ

end
end PvNP.RealizableHardness.GaussianNearOne
