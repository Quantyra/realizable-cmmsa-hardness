/- UNCOMPILED source draft: no successful Lean run or independent acceptance claimed. -/
import PvNP.RealizableHardness.GrassmannCounting
import PvNP.RealizableHardness.TripleRestrictionDimension
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace PvNP.RealizableHardness.GaussianRatio
open scoped BigOperators
open GrassmannCounting TripleRestrictionRank TripleRestrictionDimension
noncomputable section

/-- The actual independent-frame count with its leading power removed. -/
def normalizedFrame (n a : ℕ) : ℚ :=
  ∏ i ∈ Finset.range a, (1 - (2 : ℚ)^i / 2^n)

lemma sum_two_pow (a : ℕ) :
    (∑ i ∈ Finset.range a, (2 : ℚ)^i) = 2^a - 1 := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- Elementary finite product lower bound, proved without independence assumptions. -/
lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  revert hx
  induction s using Finset.induction_on with
  | empty => intro hx; simp
  | @insert i s hi ih =>
    intro hx
    have hxi := hx i (Finset.mem_insert_self i s)
    have hxs : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1 :=
      fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have hS : 0 ≤ ∑ j ∈ s, x j := Finset.sum_nonneg (fun j hj => (hxs j hj).1)
    have hmul := mul_le_mul_of_nonneg_left (ih hxs) (sub_nonneg.mpr hxi.2)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hxi.1 hS]

lemma normalizedFrame_le_one (n a : ℕ) : normalizedFrame n a ≤ 1 := by
  by_cases ha : a ≤ n
  · apply Finset.prod_le_one
    · intro i hi
      have hi' : i ≤ n := le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) ha
      have hp : (2 : ℚ)^i ≤ 2^n := pow_le_pow_right₀ (by norm_num) hi'
      exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hp)
    · intro i hi
      have h : 0 ≤ (2 : ℚ)^i / 2^n := by positivity
      linarith
  · have hn : n ∈ Finset.range a := Finset.mem_range.mpr (Nat.lt_of_not_ge ha)
    have hz : normalizedFrame n a = 0 := by
      apply Finset.prod_eq_zero hn
      simp
    rw [hz]
    norm_num

lemma normalizedFrame_ge_half (ha : a + 1 ≤ n) :
    (1 / 2 : ℚ) ≤ normalizedFrame n a := by
  have hx : ∀ i ∈ Finset.range a,
      0 ≤ (2 : ℚ)^i / 2^n ∧ (2 : ℚ)^i / 2^n ≤ 1 := by
    intro i hi
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
  have hp := one_sub_sum_le_prod (Finset.range a) (fun i => (2 : ℚ)^i / 2^n) hx
  have hpow : (2 : ℚ)^(a+1) ≤ 2^n := pow_le_pow_right₀ (by norm_num) ha
  rw [pow_succ] at hpow
  have hs : (∑ i ∈ Finset.range a, (2 : ℚ)^i / 2^n) ≤ 1/2 := by
    rw [← Finset.sum_div, sum_two_pow]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  exact le_trans (by linarith) hp

lemma cast_frameProduct (ha : a ≤ n) :
    (frameProduct n a : ℚ) = (2 : ℚ)^(n*a) * normalizedFrame n a := by
  have hf : ∀ i ∈ Finset.range a,
      ((2^n - 2^i : ℕ) : ℚ) = (2 : ℚ)^n * (1 - (2 : ℚ)^i / 2^n) := by
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hi')]
    push_cast
    field_simp
  unfold frameProduct
  rw [Fin.prod_univ_eq_prod_range (fun i => 2^n - 2^i) a]
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ Finset.range a, ((2^n - 2^i : ℕ) : ℚ)) =
        ∏ i ∈ Finset.range a, (2 : ℚ)^n * (1 - (2 : ℚ)^i / 2^n) :=
      Finset.prod_congr rfl hf
    _ = (2 : ℚ)^(n*a) * normalizedFrame n a := by
      rw [Finset.prod_mul_distrib]
      simp [normalizedFrame, ← pow_mul]

/-- Derived from actual subspace/frame double counting in the coordinate space. -/
lemma gaussian_mul_frame (ha : a ≤ n) :
    gaussian n a * frameProduct a a = frameProduct n a := by
  have h := card_grass_mul (V := Fin n → ZMod 2) (a := a) (by simpa using ha)
  simpa [card_grass, Module.finrank_pi] using h

lemma frameProduct_pos (ha : a ≤ n) : 0 < frameProduct n a := by
  apply Finset.prod_pos
  intro i hi
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (lt_of_lt_of_le i.isLt ha)

lemma gaussian_pos (ha : a ≤ n) : 0 < gaussian n a := by
  have h := gaussian_mul_frame ha
  have hp := frameProduct_pos ha
  by_contra hn
  have hz : gaussian n a = 0 := by omega
  rw [hz, zero_mul] at h
  omega

lemma gaussian_ratio_eq (ha : a ≤ m) (hm : m ≤ n) :
    (gaussian n a : ℚ) / gaussian m a =
      (2 : ℚ)^(a*(n-m)) * (normalizedFrame n a / normalizedFrame m a) := by
  have hn := le_trans ha hm
  have h1 : (gaussian n a : ℚ) * frameProduct a a =
      (2 : ℚ)^(n*a) * normalizedFrame n a := by
    rw [← cast_frameProduct hn]
    exact_mod_cast gaussian_mul_frame hn
  have h2 : (gaussian m a : ℚ) * frameProduct a a =
      (2 : ℚ)^(m*a) * normalizedFrame m a := by
    rw [← cast_frameProduct ha]
    exact_mod_cast gaussian_mul_frame ha
  have hg : (gaussian m a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (gaussian_pos ha))
  have hf : (frameProduct a a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (frameProduct_self_pos a))
  have hnorm : normalizedFrame m a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h2
    exact (mul_ne_zero hg hf) h2
  have hexp : n*a = a*(n-m) + m*a := by
    calc
      n*a = ((n-m)+m)*a := by rw [Nat.sub_add_cancel hm]
      _ = a*(n-m) + m*a := by ring
  rw [hexp, pow_add] at h1
  apply (div_eq_iff hg).mpr
  apply (mul_right_cancel₀ hf)
  rw [h1]
  field_simp [hnorm]
  have hh := congrArg (fun x => normalizedFrame n a * x) h2
  nlinarith only [hh]

/-- A concrete constant bound under one spare retained dimension. -/
lemma gaussian_ratio_le (ha : a + 1 ≤ m) (hm : m ≤ n) :
    (gaussian n a : ℚ) / gaussian m a ≤ 2 * (2 : ℚ)^(a*(n-m)) := by
  rw [gaussian_ratio_eq (by omega) hm]
  have hl := normalizedFrame_ge_half ha
  have hu := normalizedFrame_le_one n a
  have hr : normalizedFrame n a / normalizedFrame m a ≤ 2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have h := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ (2 : ℚ)^(a*(n-m)))
  simpa [mul_comm] using h

/-- Manuscript constant, with natural subtraction and its nontruncation explicit. -/
lemma retained_gaussian_ratio_le (draw : Draw J)
    (ha : a + 1 ≤ 3*J - 2*dropCount draw) :
    (gaussian (3*J) a : ℚ) /
        gaussian (Module.finrank (ZMod 2) (retained draw)) a ≤
      4 * (2 : ℚ)^(2*a*dropCount draw) := by
  rw [retained_finrank_eq]
  have hd := twice_dropCount_le draw
  have he : a * (3*J - (3*J - 2*dropCount draw)) = 2*a*dropCount draw := by
    rw [Nat.sub_sub_self hd]
    ring
  have h := gaussian_ratio_le ha (Nat.sub_le (3*J) (2*dropCount draw))
  rw [he] at h
  have hp : 0 ≤ (2 : ℚ)^(2*a*dropCount draw) := by positivity
  linarith

/-- Exactly the Gaussian factor needed after the good-marginal Bayes bound. -/
lemma retained_gaussian_twice_le_cutoff (draw : Draw J)
    (ha : a + 1 ≤ 3*J - 2*dropCount draw) (hT : dropCount draw ≤ T) :
    2 * ((gaussian (3*J) a : ℚ) /
      gaussian (Module.finrank (ZMod 2) (retained draw)) a) ≤
        8 * (2 : ℚ)^(2*a*T) := by
  have h := retained_gaussian_ratio_le draw ha
  have hp : (2 : ℚ)^(2*a*dropCount draw) ≤ 2^(2*a*T) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left (2*a) hT)
  linarith

end
end PvNP.RealizableHardness.GaussianRatio
