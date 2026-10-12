import PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
  D3c2d: source-level sampling bounds for the actual binary Grassmann incidence
  family.  The arithmetic below is derived from the finite frame product and
  the already proved incidence cardinalities.  In particular, the pair-product
  inequality is proved internally; it is not a hypothesis or a new axiom.

  This bounded increment excludes Gaussian-ratio asymptotics beyond the stated
  finite bounds, the actual enlarged-carrier/D3c2e join, advice buckets,
  Section 8, CMMSA, and any public switching/P-vs-NP claim.
-/

namespace PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds

open scoped BigOperators
open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMZ24ComplementRestriction
open PvNP.RealizableHardness.ActualBinaryGrassmannIncidence
open PvNP.RealizableHardness.ActualFiniteIncidenceSampling
open PvNP.RealizableHardness.ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def normalizedFrame (n b : Nat) : ℚ :=
  Finset.prod (Finset.range b) (fun i => 1 - (2 : ℚ)^i / 2^n)

lemma normalizedFrame_zero (n : Nat) : normalizedFrame n 0 = 1 := by
  simp [normalizedFrame]

def leadingFactor (b r : Nat) : ℚ := 1 / (2 : ℚ)^(r*b)

def frameError (n b : Nat) : ℚ := ((2 : ℚ)^b - 1) / 2^n

lemma sum_two_pow (b : Nat) :
    Finset.sum (Finset.range b) (fun i => (2 : ℚ)^i) = 2^b - 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma one_sub_sum_le_prod {α : Type*} (s : Finset α) (x : α → ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    1 - Finset.sum s x ≤ Finset.prod s (fun i => 1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hxi := hx i (Finset.mem_insert_self i s)
      have hxs : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1 :=
        fun j hj => hx j (Finset.mem_insert_of_mem hj)
      have hs : 0 ≤ Finset.sum s x := Finset.sum_nonneg (fun j hj => (hxs j hj).1)
      have hm := mul_le_mul_of_nonneg_left (ih hxs) (sub_nonneg.mpr hxi.2)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      nlinarith [mul_nonneg hxi.1 hs]

lemma normalizedFrame_nonneg {n b : Nat} (hb : b ≤ n) :
    0 ≤ normalizedFrame n b := by
  unfold normalizedFrame
  apply Finset.prod_nonneg
  intro i hi
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)

lemma normalizedFrame_le_one (n b : Nat) : normalizedFrame n b ≤ 1 := by
  by_cases hb : b ≤ n
  · unfold normalizedFrame
    apply Finset.prod_le_one
    · intro i hi
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num)
        (by have := Finset.mem_range.mp hi; omega)
    · intro i hi
      have : 0 ≤ (2 : ℚ)^i / 2^n := by positivity
      linarith
  · have hn : n ∈ Finset.range b := Finset.mem_range.mpr (Nat.lt_of_not_ge hb)
    change Finset.prod (Finset.range b)
      (fun i => 1 - (2 : ℚ)^i / 2^n) ≤ 1
    have hp : (2 : ℚ)^n ≠ 0 := by positivity
    have hz : 1 - (2 : ℚ)^n / 2^n = 0 := by
      rw [div_self hp]
      norm_num
    rw [Finset.prod_eq_zero hn hz]
    norm_num

lemma normalizedFrame_mono {b m n : Nat} (hb : b ≤ m) (hm : m ≤ n) :
    normalizedFrame m b ≤ normalizedFrame n b := by
  unfold normalizedFrame
  apply Finset.prod_le_prod
  · intro i hi
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega))
  · intro i hi
    have hp : (2 : ℚ)^m ≤ 2^n := pow_le_pow_right₀ (by norm_num) hm
    have hd : (2 : ℚ)^i / 2^n ≤ (2 : ℚ)^i / 2^m :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    linarith

lemma normalizedFrame_ge_half {b n : Nat} (hb : b + 1 ≤ n) :
    (1 / 2 : ℚ) ≤ normalizedFrame n b := by
  have hsub : b ≤ n := by omega
  have hx : ∀ i ∈ Finset.range b,
      0 ≤ (2 : ℚ)^i / 2^n ∧ (2 : ℚ)^i / 2^n ≤ 1 := by
    intro i hi
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) (by
        have hi' := Finset.mem_range.mp hi
        omega)
  have hp := one_sub_sum_le_prod (Finset.range b)
    (fun i => (2 : ℚ)^i / 2^n) hx
  have hpow : (2 : ℚ)^(b + 1) ≤ 2^n := pow_le_pow_right₀ (by norm_num) hb
  rw [pow_succ] at hpow
  have hs : Finset.sum (Finset.range b) (fun i => (2 : ℚ)^i / 2^n) ≤ 1 / 2 := by
    rw [← Finset.sum_div, sum_two_pow]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  change (1 / 2 : ℚ) ≤ Finset.prod (Finset.range b)
    (fun i => 1 - (2 : ℚ)^i / 2^n)
  linarith

lemma cast_frameProduct {b n : Nat} (hb : b ≤ n) :
    (frameProduct n b : ℚ) = (2 : ℚ)^(n*b) * normalizedFrame n b := by
  have hf : ∀ i ∈ Finset.range b,
      ((2^n - 2^i : Nat) : ℚ) = (2 : ℚ)^n *
        (1 - (2 : ℚ)^i / 2^n) := by
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hi')]
    push_cast
    field_simp
  unfold frameProduct
  rw [Fin.prod_univ_eq_prod_range (fun i => 2^n - 2^i) b]
  rw [Nat.cast_prod]
  calc
    Finset.prod (Finset.range b) (fun i => ((2^n - 2^i : Nat) : ℚ)) =
        Finset.prod (Finset.range b) (fun i => (2 : ℚ)^n *
          (1 - (2 : ℚ)^i / 2^n)) := Finset.prod_congr rfl hf
    _ = (2 : ℚ)^(n*b) * normalizedFrame n b := by
      rw [Finset.prod_mul_distrib]
      simp [normalizedFrame, ← pow_mul]

lemma gaussian_mul_frame {b n : Nat} (hb : b ≤ n) :
    gaussian n b * frameProduct b b = frameProduct n b := by
  have h := card_grass_mul (V := Fin n → ZMod 2) (a := b) (by simpa using hb)
  simpa [card_grass, Module.finrank_pi] using h

lemma frameProduct_pos {b n : Nat} (hb : b ≤ n) : 0 < frameProduct n b := by
  apply Finset.prod_pos
  intro i hi
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (lt_of_lt_of_le i.isLt hb)

lemma gaussian_pos {b n : Nat} (hb : b ≤ n) : 0 < gaussian n b := by
  exact gaussian_pos_of_le hb

lemma gaussian_ratio_eq {b m n : Nat} (hb : b ≤ m) (hm : m ≤ n) :
    (gaussian n b : ℚ) / gaussian m b =
      (2 : ℚ)^(b*(n-m)) * (normalizedFrame n b / normalizedFrame m b) := by
  have hn := le_trans hb hm
  have h1 : (gaussian n b : ℚ) * frameProduct b b =
      (2 : ℚ)^(n*b) * normalizedFrame n b := by
    rw [← cast_frameProduct hn]
    exact_mod_cast gaussian_mul_frame hn
  have h2 : (gaussian m b : ℚ) * frameProduct b b =
      (2 : ℚ)^(m*b) * normalizedFrame m b := by
    rw [← cast_frameProduct hb]
    exact_mod_cast gaussian_mul_frame hb
  have hg : (gaussian m b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (gaussian_pos hb))
  have hf : (frameProduct b b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (frameProduct_self_pos b))
  have hnorm : normalizedFrame m b ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h2
    exact (mul_ne_zero hg hf) h2
  have hexp : n*b = b*(n-m) + m*b := by
    calc
      n*b = ((n-m)+m)*b := by rw [Nat.sub_add_cancel hm]
      _ = b*(n-m) + m*b := by ring
  rw [hexp, pow_add] at h1
  apply (div_eq_iff hg).mpr
  apply (mul_right_cancel₀ hf)
  rw [h1]
  field_simp [hnorm]
  have hh := congrArg (fun x => normalizedFrame n b * x) h2
  nlinarith only [hh]

lemma gaussian_inverse_ratio_eq {b c n : Nat} (hc : c ≤ n)
    (hb : b + 1 ≤ n-c) :
    (gaussian (n-c) b : ℚ) / gaussian n b =
      leadingFactor b c *
        (normalizedFrame (n-c) b / normalizedFrame n b) := by
  have hsub : n-c ≤ n := Nat.sub_le n c
  have hnc : n-(n-c) = c := by omega
  have h := gaussian_ratio_eq (b := b) (m := n-c) (n := n)
    (by omega) hsub
  have hmn : (gaussian (n-c) b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (gaussian_pos (by omega)))
  have hn : (gaussian n b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (gaussian_pos (by omega)))
  have hfm : normalizedFrame (n-c) b ≠ 0 := by
    have hh := normalizedFrame_ge_half hb
    linarith
  have hfn : normalizedFrame n b ≠ 0 := by
    have hn : b + 1 ≤ n := le_trans hb hsub
    have hh := normalizedFrame_ge_half hn
    have hh' : (0 : ℚ) < normalizedFrame n b := by linarith
    exact ne_of_gt hh'
  have hi := congrArg (fun x : ℚ => x⁻¹) h
  simpa [leadingFactor, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
    mul_assoc, hfm, hfn, hmn, hn, hnc] using hi

lemma gaussian_ratio_lower {b m n : Nat} (hb : b + 1 ≤ m) (hm : m ≤ n) :
    leadingFactor b (n-m) / 2 ≤ (gaussian m b : ℚ) / gaussian n b := by
  have hsub : n-m ≤ n := Nat.sub_le n m
  have hnm : n-(n-m) = m := by omega
  have h := gaussian_inverse_ratio_eq (c := n-m) hsub (by simpa [hnm] using hb)
  rw [hnm] at h
  rw [h]
  have hp : 0 < normalizedFrame n b := by
    have hsub : m ≤ n := hm
    have hn : b+1 ≤ n := le_trans hb hsub
    have hi := normalizedFrame_ge_half hn
    linarith
  have hi := normalizedFrame_ge_half hb
  have hu := normalizedFrame_le_one n b
  have hq : 1 / 2 ≤ normalizedFrame m b / normalizedFrame n b := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [hi, hu]
  have hpow : (0 : ℚ) ≤ (2 : ℚ)^(b*(n-m)) := by positivity
  have hlead : 0 ≤ leadingFactor b (n-m) := by unfold leadingFactor; positivity
  have := mul_le_mul_of_nonneg_left hq hlead
  have hne : (2 : ℚ)^(b*(n-m)) ≠ 0 := by positivity
  field_simp [leadingFactor, hne] at this ⊢
  nlinarith

lemma gaussian_ratio_upper {b m n : Nat} (hb : b + 1 ≤ m) (hm : m ≤ n) :
    (gaussian n b : ℚ) / gaussian m b ≤ 2 * (2 : ℚ)^(b*(n-m)) := by
  rw [gaussian_ratio_eq (by omega) hm]
  have hp : 0 < normalizedFrame m b := by
    have h := normalizedFrame_ge_half hb
    linarith
  have hu := normalizedFrame_le_one n b
  have hq : normalizedFrame n b / normalizedFrame m b ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    have hl := normalizedFrame_ge_half hb
    nlinarith [hl, hu]
  nlinarith [mul_le_mul_of_nonneg_left hq
    (show (0 : ℚ) ≤ (2 : ℚ)^(b*(n-m)) by positivity)]

lemma gaussian_near_one_127_128 {b n r : Nat}
    (hr : r ≤ n) (hspare : b + 7 ≤ n-r) :
    (127 / 128 : ℚ) * leadingFactor b r ≤
      (gaussian (n-r) b : ℚ) / gaussian n b ∧
      (gaussian (n-r) b : ℚ) / gaussian n b ≤ leadingFactor b r := by
  rw [gaussian_inverse_ratio_eq (c := r) hr (by omega)]
  have hfn : 0 < normalizedFrame n b := by
    have h := normalizedFrame_ge_half (show b+1 ≤ n by omega)
    linarith
  have hupper := normalizedFrame_le_one n b
  have hfm : 0 < normalizedFrame (n-r) b := by
    have h := normalizedFrame_ge_half (show b+1 ≤ n-r by omega)
    linarith
  have hmono : normalizedFrame (n-r) b / normalizedFrame n b ≤ 1 := by
    exact (div_le_one hfn).mpr (normalizedFrame_mono (by omega) (Nat.sub_le _ _))
  have herr : (1 / 128 : ℚ) ≥
      frameError (n-r) b := by
    unfold frameError
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2^(n-r))).mpr
    have he : (2 : ℚ)^(b+7) ≤ 2^(n-r) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_add] at he
    norm_num at he ⊢
    nlinarith [he]
  have hlow : (127 / 128 : ℚ) ≤
      normalizedFrame (n-r) b / normalizedFrame n b := by
    have hs := one_sub_sum_le_prod (Finset.range b)
      (fun i => (2 : ℚ)^i / 2^(n-r)) (by
        intro i hi
        constructor
        · positivity
        · exact (div_le_one (by positivity)).mpr
            (pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)))
    have he := herr
    have hh : 1 - frameError (n-r) b ≤ normalizedFrame (n-r) b := by
      simpa [normalizedFrame, frameError, ← Finset.sum_div, sum_two_pow] using hs
    apply (le_div_iff₀ hfn).mpr
    nlinarith [hh, hupper]
  constructor
  · have := mul_le_mul_of_nonneg_left hlow
      (show (0 : ℚ) ≤ leadingFactor b r by unfold leadingFactor; positivity)
    field_simp [show (2 : ℚ)^(b*r) ≠ 0 by positivity] at this ⊢
    nlinarith
  · have := mul_le_mul_of_nonneg_left hmono
      (show (0 : ℚ) ≤ leadingFactor b r by unfold leadingFactor; positivity)
    field_simp [show (2 : ℚ)^(b*r) ≠ 0 by positivity] at this ⊢
    nlinarith

/- The following finite-product lemma is the force-bearing step used by both
   bottom and pointed pair-subindependence. -/
lemma normalizedFrame_pair_product_le {b n r : Nat}
    (hgate : b ≤ n - 2*r) :
    normalizedFrame (n-2*r) b * normalizedFrame n b ≤
      normalizedFrame (n-r) b ^ 2 := by
  classical
  unfold normalizedFrame
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro i hi
    have hbpos : i < b := Finset.mem_range.mp hi
    have h2r : 2*r ≤ n := by omega
    have hi' : i ≤ n - 2*r := by
      omega
    have hA : 0 < (2 : ℚ)^(n-2*r) := by positivity
    have hB : 0 < (2 : ℚ)^(n-r) := by positivity
    have hC : 0 < (2 : ℚ)^n := by positivity
    have hia : (2 : ℚ)^i ≤ 2^(n-2*r) :=
      pow_le_pow_right₀ (by norm_num) hi'
    have hib : (2 : ℚ)^i ≤ 2^(n-r) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    have hic : (2 : ℚ)^i ≤ 2^n := by
      apply pow_le_pow_right₀ (by norm_num); omega
    exact mul_nonneg
      (sub_nonneg.mpr ((div_le_one hA).mpr hia))
      (sub_nonneg.mpr ((div_le_one hC).mpr hic))
  · intro i hi
    have hbpos : i < b := Finset.mem_range.mp hi
    have h2r : 2*r ≤ n := by omega
    have hi' : i ≤ n - 2*r := by
      omega
    have hA : 0 < (2 : ℚ)^(n-2*r) := by positivity
    have hB : 0 < (2 : ℚ)^(n-r) := by positivity
    have hC : 0 < (2 : ℚ)^n := by positivity
    have hia : (2 : ℚ)^i ≤ 2^(n-2*r) :=
      pow_le_pow_right₀ (by norm_num) hi'
    have hib : (2 : ℚ)^i ≤ 2^(n-r) := by
      apply pow_le_pow_right₀ (by norm_num); omega
    have hic : (2 : ℚ)^i ≤ 2^n := by
      apply pow_le_pow_right₀ (by norm_num); omega
    have hfactor :
        (1 - (2 : ℚ)^i / 2^(n-2*r)) * (1 - (2 : ℚ)^i / 2^n) ≤
          (1 - (2 : ℚ)^i / 2^(n-r)) ^ 2 := by
      have hrel : ((2 : ℚ)^(n-2*r)) * ((2 : ℚ)^n) =
          ((2 : ℚ)^(n-r))^2 := by
        rw [← pow_add, pow_two, ← pow_add]
        congr 1
        omega
      have hmul : (2 : ℚ)^(n-2*r) *
          (2*(2 : ℚ)^(n-r) - (2 : ℚ)^(n-2*r) - (2 : ℚ)^n) ≤ 0 := by
        nlinarith [sq_nonneg ((2 : ℚ)^(n-r) - (2 : ℚ)^(n-2*r)), hrel]
      have hmid : 2*(2 : ℚ)^(n-r) ≤
          (2 : ℚ)^(n-2*r) + (2 : ℚ)^n := by
        by_contra hnot
        have hd : 0 < 2*(2 : ℚ)^(n-r) -
            (2 : ℚ)^(n-2*r) - (2 : ℚ)^n := by linarith
        have hp := mul_pos hA hd
        linarith
      have hx : (0 : ℚ) ≤ (2 : ℚ)^i *
          ((2 : ℚ)^(n-2*r) + (2 : ℚ)^n - 2*(2 : ℚ)^(n-r)) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hmid)
      field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
      nlinarith [hrel, hx]
    exact hfactor

theorem gaussian_pair_product_le {b n r : Nat}
    (hgate : b ≤ n - 2*r) :
    gaussian (n-2*r) b * gaussian n b ≤ gaussian (n-r) b ^ 2 := by
  by_cases hb0 : b = 0
  · simp [hb0, gaussian_zero]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have h2r : 2*r ≤ n := by omega
    have hsmall : b ≤ n - 2*r := hgate
    have h1 := gaussian_mul_frame hsmall
    have h2 := gaussian_mul_frame (show b ≤ n by omega)
    have h3 := gaussian_mul_frame (show b ≤ n-r by omega)
    have hc1 := cast_frameProduct hsmall
    have hc2 := cast_frameProduct (show b ≤ n by omega)
    have hc3 := cast_frameProduct (show b ≤ n-r by omega)
    have hprod := normalizedFrame_pair_product_le hgate
    have hfp : (0 : ℚ) < frameProduct b b := by exact_mod_cast frameProduct_self_pos b
    have hdim : (n-2*r)+n = (n-r)+(n-r) := by omega
    have hsum : (n-2*r)*b + n*b = (n-r)*b + (n-r)*b := by
      calc
        _ = ((n-2*r)+n)*b := by rw [add_mul]
        _ = ((n-r)+(n-r))*b := by rw [hdim]
        _ = _ := by rw [add_mul]
    have hpow : (2 : ℚ)^((n-2*r)*b + n*b) =
        ((2 : ℚ)^((n-r)*b))^2 := by
      rw [hsum, pow_add, pow_two]
    have hscaled := mul_le_mul_of_nonneg_left hprod
      (show (0 : ℚ) ≤ (2 : ℚ)^((n-2*r)*b + n*b) by positivity)
    have h1q : (gaussian (n-2*r) b : ℚ) * frameProduct b b =
        (2 : ℚ)^((n-2*r)*b) * normalizedFrame (n-2*r) b := by
      rw [← hc1]
      exact_mod_cast h1
    have h2q : (gaussian n b : ℚ) * frameProduct b b =
        (2 : ℚ)^(n*b) * normalizedFrame n b := by
      rw [← hc2]
      exact_mod_cast h2
    have h3q : (gaussian (n-r) b : ℚ) * frameProduct b b =
        (2 : ℚ)^((n-r)*b) * normalizedFrame (n-r) b := by
      rw [← hc3]
      exact_mod_cast h3
    have hmul :
        ((gaussian (n-2*r) b : ℚ) * gaussian n b) *
            (frameProduct b b : ℚ)^2 ≤
          (gaussian (n-r) b : ℚ)^2 * (frameProduct b b : ℚ)^2 := by
      calc
        _ = ((gaussian (n-2*r) b : ℚ) * frameProduct b b) *
            ((gaussian n b : ℚ) * frameProduct b b) := by ring
        _ = ((2 : ℚ)^((n-2*r)*b) * normalizedFrame (n-2*r) b) *
            ((2 : ℚ)^(n*b) * normalizedFrame n b) := by rw [h1q, h2q]
        _ = (2 : ℚ)^((n-2*r)*b + n*b) *
            (normalizedFrame (n-2*r) b * normalizedFrame n b) := by
          rw [pow_add]
          ring
        _ ≤ (2 : ℚ)^((n-2*r)*b + n*b) *
            normalizedFrame (n-r) b ^ 2 := hscaled
        _ = ((2 : ℚ)^((n-r)*b) * normalizedFrame (n-r) b)^2 := by
          rw [hpow]
          ring
        _ = ((gaussian (n-r) b : ℚ) * frameProduct b b)^2 := by rw [h3q]
        _ = _ := by ring
    have hf2 : 0 < (frameProduct b b : ℚ)^2 := sq_pos_of_pos hfp
    have hrat : (gaussian (n-2*r) b : ℚ) * gaussian n b ≤
        (gaussian (n-r) b : ℚ)^2 := by
      by_contra hnot
      have hlt : (gaussian (n-r) b : ℚ)^2 <
          (gaussian (n-2*r) b : ℚ) * gaussian n b := lt_of_not_ge hnot
      have hmul' := mul_lt_mul_of_pos_right hlt hf2
      nlinarith [hmul, hmul']
    exact_mod_cast hrat

theorem gaussian_probability_bounds {b n r : Nat}
    (hr : r ≤ n) (hspare : b + 7 ≤ n-r) :
    (127 / 128 : ℚ) / (2 : ℚ)^(r*b) ≤
        (gaussian (n-r) b : ℚ) / gaussian n b ∧
      (gaussian (n-r) b : ℚ) / gaussian n b ≤ 1 / (2 : ℚ)^(r*b) := by
  simpa [leadingFactor, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using gaussian_near_one_127_128 (b := b) (n := n) (r := r) (by omega) hspare

theorem gaussian_probability_ge_half {b n r : Nat}
    (hr : r ≤ n) (hspare : b + 1 ≤ n-r) :
    (1 / 2 : ℚ) / (2 : ℚ)^(r*b) ≤
      (gaussian (n-r) b : ℚ) / gaussian n b := by
  have hsub : n-(n-r) = r := by omega
  have h := gaussian_ratio_lower (by simpa [hsub] using hspare) (Nat.sub_le n r)
  simpa [hsub, leadingFactor, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using h

theorem gaussian_probability_ge_inv_nine {b n r : Nat}
    (hr : r ≤ n) (hspare : b + 1 ≤ n-r) :
    (1 / 9 : ℚ) / (2 : ℚ)^(r*b) ≤
      (gaussian (n-r) b : ℚ) / gaussian n b := by
  have h := gaussian_probability_ge_half (b := b) (n := n) (r := r) (by omega) hspare
  calc
    (1 / 9 : ℚ) / (2 : ℚ)^(r*b) ≤
        (1 / 2 : ℚ) / (2 : ℚ)^(r*b) := by
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ (gaussian (n-r) b : ℚ) / gaussian n b := h

theorem bottom_incidenceProbability {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {r b : Nat} (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    incidenceProbability (bottomRegularIncidence W hW hb) =
      (gaussian (Module.finrank (ZMod 2) V-r) b : ℚ) /
        gaussian (Module.finrank (ZMod 2) V) b := by
  have hgoal : Fintype.card (BottomQuery V b) =
      gaussian (Module.finrank (ZMod 2) V) b := bottomCarrier_card_fintype b
  unfold incidenceProbability bottomRegularIncidence
  simpa [hgoal]

theorem bottom_incidenceProbability_ge_inv_nine {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {r b : Nat} (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : b ≤ Module.finrank (ZMod 2) V - 2*r)
    (hspare : b + 1 ≤ Module.finrank (ZMod 2) V-r) :
    (1/9 : ℚ) / (2 : ℚ)^(r*b) ≤
      incidenceProbability (bottomRegularIncidence W hW hgate) := by
  rw [bottom_incidenceProbability W hW hInj hgate]
  have hr : r ≤ Module.finrank (ZMod 2) V := by omega
  exact gaussian_probability_ge_inv_nine hr hspare

theorem bottom_incidenceMean {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {r b : Nat} (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    incidenceMean (bottomRegularIncidence W hW hb) =
      (Fintype.card I : ℚ) *
        ((gaussian (Module.finrank (ZMod 2) V-r) b : ℚ) /
          gaussian (Module.finrank (ZMod 2) V) b) := by
  unfold incidenceMean
  have hu := bottom_incidenceProbability W hW hInj hb
  simpa [incidenceMean, hu]

theorem bottom_pairSubindependent {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {r b : Nat} (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    PairSubindependent (bottomRegularIncidence W hW hb) := by
  classical
  unfold PairSubindependent
  intro i j hij
  have hc : incidencePairCount (bottomRegularIncidence W hW hb) i j =
      gaussian (Module.finrank (ZMod 2) V - 2*r) b := by
    unfold incidencePairCount
    rw [← Nat.card_eq_fintype_card]
    simpa [bottomRegularIncidence, bottomPairContained, bottomContained] using
      bottom_pair_count_nat (b := b) (r := r) hW hij
  rw [hc, bottomCarrier_card_fintype]
  exact gaussian_pair_product_le hb

theorem bottom_incidenceVariance_le_mean {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    [Nonempty I] {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V)
    (hW : TwoGeneric W r) (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    incidenceVariance (bottomRegularIncidence W hW hb) ≤
      incidenceMean (bottomRegularIncidence W hW hb) := by
  apply incidenceVariance_le_mean
  exact bottom_pairSubindependent W hW hInj hb

theorem bottom_incidenceSecondMoment_le {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    [Nonempty I] {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V)
    (hW : TwoGeneric W r) (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    incidenceSecondMoment (bottomRegularIncidence W hW hb) ≤
      incidenceMean (bottomRegularIncidence W hW hb)^2 +
        incidenceMean (bottomRegularIncidence W hW hb) := by
  apply incidenceSecondMoment_pair_subindependent
  exact bottom_pairSubindependent W hW hInj hb

theorem bottom_mean_mul_tv_sq_le_one {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    [Nonempty I] {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V)
    (hW : TwoGeneric W r) (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    incidenceMean (bottomRegularIncidence W hW hb) *
      totalVariation (uniformLaw (BottomQuery V b))
        (incidenceMixture (bottomRegularIncidence W hW hb)) ^ 2 ≤ 1 := by
  apply mean_mul_tv_sq_le_one
  exact bottom_pairSubindependent W hW hInj hb

theorem bottom_tv_sq_le_inv_mean {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) :
    totalVariation (uniformLaw (BottomQuery V b))
        (incidenceMixture (bottomRegularIncidence W hW hb)) ^ 2 ≤
      1 / incidenceMean (bottomRegularIncidence W hW hb) := by
  apply tv_sq_le_inv_mean
  exact bottom_pairSubindependent W hW hInj hb

theorem bottom_tv_sq_le_nine_dyadic {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : b ≤ Module.finrank (ZMod 2) V - 2*r)
    (hspare : b + 1 ≤ Module.finrank (ZMod 2) V-r) :
    totalVariation (uniformLaw (BottomQuery V b))
        (incidenceMixture (bottomRegularIncidence W hW hgate)) ^ 2 ≤
      9 * (2 : ℚ)^(r*b) / Fintype.card I := by
  have ht := bottom_tv_sq_le_inv_mean W hW hInj hgate
  have hp := bottom_incidenceProbability_ge_inv_nine W hW hInj hgate hspare
  rw [bottom_incidenceProbability W hW hInj hgate] at hp
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmu : 0 < incidenceMean (bottomRegularIncidence W hW hgate) :=
    incidenceMean_pos (bottomRegularIncidence W hW hgate)
  have hmeanLower : (Fintype.card I : ℚ) / (9 * (2 : ℚ)^(r*b)) ≤
      incidenceMean (bottomRegularIncidence W hW hgate) := by
    rw [bottom_incidenceMean W hW hInj hgate]
    calc
      (Fintype.card I : ℚ) / (9 * (2 : ℚ)^(r*b)) =
          (Fintype.card I : ℚ) * ((1/9 : ℚ) / (2 : ℚ)^(r*b)) := by ring
      _ ≤ (Fintype.card I : ℚ) *
          ((gaussian (Module.finrank (ZMod 2) V-r) b : ℚ) /
            gaussian (Module.finrank (ZMod 2) V) b) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
  have hcross0 :=
    (div_le_iff₀ (by positivity : 0 < 9 * (2 : ℚ)^(r*b))).mp hmeanLower
  have hcross : (Fintype.card I : ℚ) ≤
      9 * (2 : ℚ)^(r*b) * incidenceMean (bottomRegularIncidence W hW hgate) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross0
  have hrecip : 1 / incidenceMean (bottomRegularIncidence W hW hgate) ≤
      9 * (2 : ℚ)^(r*b) / Fintype.card I := by
    apply (div_le_div_iff₀ hmu hI).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  exact le_trans ht hrecip

theorem bottom_division_free_chebyshev {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) {epsilon : ℚ} (heps : 0 < epsilon) :
    epsilon^2 * incidenceMean (bottomRegularIncidence W hW hb) *
      eventMass (uniformLaw (BottomQuery V b))
        (relativeDeviationEvent (bottomRegularIncidence W hW hb) epsilon) ≤ 1 := by
  exact division_free_chebyshev (bottomRegularIncidence W hW hb)
    (bottom_pairSubindependent W hW hInj hb) heps

theorem bottom_rational_chebyshev {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hb : b ≤ Module.finrank (ZMod 2) V - 2*r) {epsilon : ℚ} (heps : 0 < epsilon) :
    eventMass (uniformLaw (BottomQuery V b))
        (relativeDeviationEvent (bottomRegularIncidence W hW hb) epsilon) ≤
      1 / (epsilon^2 * incidenceMean (bottomRegularIncidence W hW hb)) := by
  exact rational_chebyshev (bottomRegularIncidence W hW hb)
    (bottom_pairSubindependent W hW hInj hb) heps

theorem bottom_dyadic_mean_bounds {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    [Nonempty I] {r b : Nat} (W : I → Submodule (ZMod 2) V)
    (hW : TwoGeneric W r) (hInj : Function.Injective W)
    (hgate : b ≤ Module.finrank (ZMod 2) V - 2*r)
    (hspare : b + 7 ≤ Module.finrank (ZMod 2) V-r) :
    (Fintype.card I : ℚ) * ((127 / 128 : ℚ) / (2 : ℚ)^(r*b)) ≤
      incidenceMean (bottomRegularIncidence W hW hgate) ∧
    incidenceMean (bottomRegularIncidence W hW hgate) ≤
      (Fintype.card I : ℚ) / (2 : ℚ)^(r*b) := by
  rw [bottom_incidenceMean W hW hInj hgate]
  have hp := gaussian_probability_bounds (b := b)
    (n := Module.finrank (ZMod 2) V) (r := r) (by omega) hspare
  constructor
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hp.1 (by positivity)
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hp.2 (by positivity)

def dyadicMean (cardI r b : Nat) : ℚ :=
  (cardI : ℚ) / (2 : ℚ)^(r*b)

def bottomBadWindow {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [Fintype I] [Nonempty I]
    (r b : Nat) (R : RegularIncidence I (BottomQuery V b)) : Finset (BottomQuery V b) :=
  Finset.univ.filter (fun x =>
    (19/20 : ℚ) * dyadicMean (Fintype.card I) r b ≤
        (incidenceCount R x : ℚ) ∧
      (incidenceCount R x : ℚ) ≤
        (21/20 : ℚ) * dyadicMean (Fintype.card I) r b)

def bottomBadWindowComplement {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    (r b : Nat) (R : RegularIncidence I (BottomQuery V b)) : Finset (BottomQuery V b) :=
  Finset.univ.filter (fun x =>
    (incidenceCount R x : ℚ) <
        (19/20 : ℚ) * dyadicMean (Fintype.card I) r b ∨
      (21/20 : ℚ) * dyadicMean (Fintype.card I) r b <
        (incidenceCount R x : ℚ))

theorem bottom_badWindow_subset {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : b ≤ Module.finrank (ZMod 2) V - 2*r)
    (hspare : b + 7 ≤ Module.finrank (ZMod 2) V-r) :
    bottomBadWindowComplement r b (bottomRegularIncidence W hW hgate) ⊆
      relativeDeviationEvent (bottomRegularIncidence W hW hgate) (1/25) := by
  intro x hx
  simp only [bottomBadWindowComplement, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [relativeDeviationEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmean := bottom_dyadic_mean_bounds W hW hInj hgate hspare
  have hlow := hmean.1
  have hupp := hmean.2
  have hlow' : (127/128 : ℚ) * dyadicMean (Fintype.card I) r b ≤
      incidenceMean (bottomRegularIncidence W hW hgate) := by
    simpa [dyadicMean, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlow
  have hupp' : incidenceMean (bottomRegularIncidence W hW hgate) ≤
      dyadicMean (Fintype.card I) r b := by
    simpa [dyadicMean] using hupp
  rcases hx with hx | hx
  · have hc : (incidenceCount (bottomRegularIncidence W hW hgate) x : ℚ) ≤
        incidenceMean (bottomRegularIncidence W hW hgate) := by
      nlinarith [hlow', hupp']
    rw [abs_of_nonpos (sub_nonpos.mpr hc)]
    nlinarith [hlow', hupp']
  · have hc : incidenceMean (bottomRegularIncidence W hW hgate) ≤
        (incidenceCount (bottomRegularIncidence W hW hgate) x : ℚ) := by
      nlinarith [hlow', hupp']
    rw [abs_of_nonneg (sub_nonneg.mpr hc)]
    nlinarith [hlow', hupp']

theorem bottom_badWindow_concentration {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {r b : Nat} [Nonempty (BottomQuery V b)]
    (W : I → Submodule (ZMod 2) V) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : b ≤ Module.finrank (ZMod 2) V - 2*r)
    (hspare : b + 7 ≤ Module.finrank (ZMod 2) V-r) :
    eventMass (uniformLaw (BottomQuery V b))
      (bottomBadWindowComplement r b (bottomRegularIncidence W hW hgate)) ≤
      630 * (2 : ℚ)^(r*b) / Fintype.card I := by
  have hsub := bottom_badWindow_subset W hW hInj hgate hspare
  have hmass : eventMass (uniformLaw (BottomQuery V b))
      (bottomBadWindowComplement r b (bottomRegularIncidence W hW hgate)) ≤
      eventMass (uniformLaw (BottomQuery V b))
        (relativeDeviationEvent (bottomRegularIncidence W hW hgate) (1/25)) := by
    unfold eventMass
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x hx hxnot
    exact (uniformLaw (BottomQuery V b)).nonneg x
  have hcheb := bottom_rational_chebyshev W hW hInj hgate
    (by norm_num : (0 : ℚ) < 1/25)
  have hmean := bottom_dyadic_mean_bounds W hW hInj hgate hspare
  have hpos : 0 < incidenceMean (bottomRegularIncidence W hW hgate) :=
    incidenceMean_pos (bottomRegularIncidence W hW hgate)
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ eventMass (uniformLaw (BottomQuery V b))
        (relativeDeviationEvent (bottomRegularIncidence W hW hgate) (1/25)) := hmass
    _ ≤ 1 / ((1/25 : ℚ)^2 * incidenceMean (bottomRegularIncidence W hW hgate)) := hcheb
    _ ≤ 630 * (2 : ℚ)^(r*b) / Fintype.card I := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hpos)).mpr
      have hlow := hmean.1
      have hp : 0 < (2 : ℚ)^(r*b) := by positivity
      have hlow' : (Fintype.card I : ℚ) * (127/128 : ℚ) /
          (2 : ℚ)^(r*b) ≤ incidenceMean (bottomRegularIncidence W hW hgate) := by
        convert hlow using 1 <;> ring
      have hcross : (Fintype.card I : ℚ) * (127/128 : ℚ) ≤
          (2 : ℚ)^(r*b) * incidenceMean (bottomRegularIncidence W hW hgate) :=
        by simpa [mul_assoc, mul_left_comm, mul_comm] using (div_le_iff₀ hp).mp hlow'
      have hbound : (Fintype.card I : ℚ) ≤
          ((2 : ℚ)^(r*b) * incidenceMean
            (bottomRegularIncidence W hW hgate)) / (127/128 : ℚ) :=
        (le_div_iff₀ (by norm_num : (0 : ℚ) < 127/128)).2 hcross
      have hcoef : (1 : ℚ) / (127/128) ≤ 630/625 := by norm_num
      have hscaled : (Fintype.card I : ℚ) ≤
          (630/625 : ℚ) * ((2 : ℚ)^(r*b) *
            incidenceMean (bottomRegularIncidence W hW hgate)) := by
        calc
          (Fintype.card I : ℚ) ≤
              ((2 : ℚ)^(r*b) * incidenceMean
                (bottomRegularIncidence W hW hgate)) / (127/128 : ℚ) := hbound
          _ = ((1 : ℚ) / (127/128)) *
              ((2 : ℚ)^(r*b) * incidenceMean
                (bottomRegularIncidence W hW hgate)) := by ring
          _ ≤ (630/625 : ℚ) * ((2 : ℚ)^(r*b) *
              incidenceMean (bottomRegularIncidence W hW hgate)) :=
                mul_le_mul_of_nonneg_right hcoef (by positivity)
      have hscaled' : (Fintype.card I : ℚ) ≤
          630 * (2 : ℚ)^(r*b) * ((1/25 : ℚ)^2 *
            incidenceMean (bottomRegularIncidence W hW hgate)) := by
        convert hscaled using 1 <;> norm_num <;> ring
      have htarget : 1 ≤ (630 * (2 : ℚ)^(r*b) *
          ((1/25 : ℚ)^2 * incidenceMean
            (bottomRegularIncidence W hW hgate))) / Fintype.card I := by
        apply (le_div_iff₀ hI).2
        simpa only [one_mul] using hscaled'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using htarget

/- Pointed wrappers use the same shared complement carrier and the intrinsic
   pointed incidence relation from D3c2c. -/
theorem pointed_incidenceProbability {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {a r j : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    incidenceProbability (pointedRegularIncidence C W haj hQW hW hgate) =
      (gaussian (Module.finrank (ZMod 2) V-a-r) (j-a) : ℚ) /
        gaussian (Module.finrank (ZMod 2) V-a) (j-a) := by
  have hgoal : Fintype.card (PointedQuery Q j) =
      gaussian (Module.finrank (ZMod 2) V-a) (j-a) := by
    rw [pointedCarrier_card_fintype C j]
    simp [haj, adviceComplement_finrank C]
  unfold incidenceProbability pointedRegularIncidence
  rw [hgoal]

theorem pointed_incidenceProbability_ge_inv_nine {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {a r j : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r)
    (hspare : j-a+1 ≤ Module.finrank (ZMod 2) C.A-r) :
    (1/9 : ℚ) / (2 : ℚ)^(r*(j-a)) ≤
      incidenceProbability (pointedRegularIncidence C W haj hQW hW hgate) := by
  rw [pointed_incidenceProbability C W haj hQW hW hInj hgate]
  have hr : r ≤ Module.finrank (ZMod 2) C.A := by omega
  have hp := gaussian_probability_ge_inv_nine (b := j-a)
    (n := Module.finrank (ZMod 2) C.A) (r := r) hr hspare
  simpa [adviceComplement_finrank C] using hp

theorem pointed_incidenceMean {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {a r j : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) =
      (Fintype.card I : ℚ) *
        ((gaussian (Module.finrank (ZMod 2) V-a-r) (j-a) : ℚ) /
          gaussian (Module.finrank (ZMod 2) V-a) (j-a)) := by
  unfold incidenceMean
  have hu := pointed_incidenceProbability C W haj hQW hW hInj hgate
  simpa [incidenceMean, hu]

theorem pointed_pairSubindependent {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I]
    {a r j : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    PairSubindependent (pointedRegularIncidence C W haj hQW hW hgate) := by
  classical
  unfold PairSubindependent
  intro i k hik
  have hc : incidencePairCount
      (pointedRegularIncidence C W haj hQW hW hgate) i k =
      gaussian (Module.finrank (ZMod 2) C.A - 2*r) (j-a) := by
    unfold incidencePairCount
    rw [← Nat.card_eq_fintype_card]
    have hnat := pointed_pair_count_nat (j := j) (r := r) C W hQW hW hik
    simp only [if_pos haj] at hnat
    have hg := adviceComplement_finrank C
    change Nat.card {L : PointedQuery Q j //
      pointedContained W i L ∧ pointedContained W k L} =
        gaussian (Module.finrank (ZMod 2) C.A - 2*r) (j-a)
    simpa [hg, pointedPairContained, pointedContained] using hnat
  rw [hc, pointedCarrier_card_fintype C j]
  have hp := gaussian_pair_product_le (n := Module.finrank (ZMod 2) C.A)
    (b := j-a) (r := r) (by omega)
  simpa [pointedRegularIncidence, haj, adviceComplement_finrank C] using hp

theorem pointed_incidenceVariance_le_mean {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    incidenceVariance (pointedRegularIncidence C W haj hQW hW hgate) ≤
      incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
  apply incidenceVariance_le_mean
  exact pointed_pairSubindependent C W haj hQW hW hInj hgate

theorem pointed_incidenceSecondMoment_le {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    incidenceSecondMoment (pointedRegularIncidence C W haj hQW hW hgate) ≤
      incidenceMean (pointedRegularIncidence C W haj hQW hW hgate)^2 +
        incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
  apply incidenceSecondMoment_pair_subindependent
  exact pointed_pairSubindependent C W haj hQW hW hInj hgate

theorem pointed_mean_mul_tv_sq_le_one {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) *
      totalVariation (uniformLaw (PointedQuery Q j))
        (incidenceMixture (pointedRegularIncidence C W haj hQW hW hgate)) ^ 2 ≤ 1 := by
  apply mean_mul_tv_sq_le_one
  exact pointed_pairSubindependent C W haj hQW hW hInj hgate

theorem pointed_tv_sq_le_inv_mean {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) :
    totalVariation (uniformLaw (PointedQuery Q j))
        (incidenceMixture (pointedRegularIncidence C W haj hQW hW hgate)) ^ 2 ≤
      1 / incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
  apply tv_sq_le_inv_mean
  exact pointed_pairSubindependent C W haj hQW hW hInj hgate

theorem pointed_tv_sq_le_nine_dyadic {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r)
    (hspare : j-a+1 ≤ Module.finrank (ZMod 2) C.A-r) :
    totalVariation (uniformLaw (PointedQuery Q j))
        (incidenceMixture (pointedRegularIncidence C W haj hQW hW hgate)) ^ 2 ≤
      9 * (2 : ℚ)^(r*(j-a)) / Fintype.card I := by
  have ht := pointed_tv_sq_le_inv_mean C W haj hQW hW hInj hgate
  have hr : r ≤ Module.finrank (ZMod 2) C.A := by omega
  have hpC := gaussian_probability_ge_inv_nine (b := j-a)
    (n := Module.finrank (ZMod 2) C.A) (r := r) hr hspare
  have hp : (1/9 : ℚ) / (2 : ℚ)^(r*(j-a)) ≤
      (gaussian (Module.finrank (ZMod 2) V-a-r) (j-a) : ℚ) /
        gaussian (Module.finrank (ZMod 2) V-a) (j-a) := by
    simpa [adviceComplement_finrank C] using hpC
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmu : 0 < incidenceMean
      (pointedRegularIncidence C W haj hQW hW hgate) :=
    incidenceMean_pos (pointedRegularIncidence C W haj hQW hW hgate)
  have hmeanLower : (Fintype.card I : ℚ) / (9 * (2 : ℚ)^(r*(j-a))) ≤
      incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
    rw [pointed_incidenceMean C W haj hQW hW hInj hgate]
    calc
      (Fintype.card I : ℚ) / (9 * (2 : ℚ)^(r*(j-a))) =
          (Fintype.card I : ℚ) * ((1/9 : ℚ) / (2 : ℚ)^(r*(j-a))) := by ring
      _ ≤ (Fintype.card I : ℚ) *
          ((gaussian (Module.finrank (ZMod 2) V-a-r) (j-a) : ℚ) /
            gaussian (Module.finrank (ZMod 2) V-a) (j-a)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
  have hcross0 :=
    (div_le_iff₀ (by positivity : 0 < 9 * (2 : ℚ)^(r*(j-a)))).mp hmeanLower
  have hcross : (Fintype.card I : ℚ) ≤
      9 * (2 : ℚ)^(r*(j-a)) *
        incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross0
  have hrecip : 1 / incidenceMean
      (pointedRegularIncidence C W haj hQW hW hgate) ≤
      9 * (2 : ℚ)^(r*(j-a)) / Fintype.card I := by
    apply (div_le_div_iff₀ hmu hI).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
  exact le_trans ht hrecip

theorem pointed_division_free_chebyshev {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) {epsilon : ℚ}
    (heps : 0 < epsilon) :
    epsilon^2 * incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) *
      eventMass (uniformLaw (PointedQuery Q j))
        (relativeDeviationEvent (pointedRegularIncidence C W haj hQW hW hgate) epsilon) ≤ 1 := by
  exact division_free_chebyshev (pointedRegularIncidence C W haj hQW hW hgate)
    (pointed_pairSubindependent C W haj hQW hW hInj hgate) heps

theorem pointed_rational_chebyshev {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r) {epsilon : ℚ}
    (heps : 0 < epsilon) :
    eventMass (uniformLaw (PointedQuery Q j))
        (relativeDeviationEvent (pointedRegularIncidence C W haj hQW hW hgate) epsilon) ≤
      1 / (epsilon^2 * incidenceMean (pointedRegularIncidence C W haj hQW hW hgate)) := by
  exact rational_chebyshev (pointedRegularIncidence C W haj hQW hW hgate)
    (pointed_pairSubindependent C W haj hQW hW hInj hgate) heps

theorem pointed_dyadic_mean_bounds {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} (C : AdviceComplement Q)
    (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A - 2*r)
    (hspare : j-a + 7 ≤ Module.finrank (ZMod 2) C.A-r) :
    (Fintype.card I : ℚ) * ((127/128 : ℚ) / (2 : ℚ)^(r*(j-a))) ≤
      incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) ∧
    incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) ≤
      (Fintype.card I : ℚ) / (2 : ℚ)^(r*(j-a)) := by
  rw [pointed_incidenceMean C W haj hQW hW hInj hgate]
  have hr : r ≤ Module.finrank (ZMod 2) C.A := by omega
  have hpC := gaussian_probability_bounds (n := Module.finrank (ZMod 2) C.A)
    (b := j-a) (r := r) hr hspare
  have hp := by simpa [adviceComplement_finrank C] using hpC
  constructor
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hp.1 (by positivity)
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hp.2 (by positivity)

def pointedBadWindowComplement {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (r : Nat) (R : RegularIncidence I (PointedQuery Q j)) : Finset (PointedQuery Q j) :=
  Finset.univ.filter (fun x =>
    (incidenceCount R x : ℚ) <
        (19/20 : ℚ) * dyadicMean (Fintype.card I) r (j-a) ∨
      (21/20 : ℚ) * dyadicMean (Fintype.card I) r (j-a) <
        (incidenceCount R x : ℚ))

theorem pointed_badWindow_subset {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A-2*r)
    (hspare : j-a + 7 ≤ Module.finrank (ZMod 2) C.A-r) :
    pointedBadWindowComplement r (pointedRegularIncidence C W haj hQW hW hgate) ⊆
      relativeDeviationEvent (pointedRegularIncidence C W haj hQW hW hgate) (1/25) := by
  intro x hx
  simp only [pointedBadWindowComplement, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [relativeDeviationEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmean := pointed_dyadic_mean_bounds C W haj hQW hW hInj hgate hspare
  have hlow := hmean.1
  have hupp := hmean.2
  have hlow' : (127/128 : ℚ) * dyadicMean (Fintype.card I) r (j-a) ≤
      incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
    simpa [dyadicMean, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlow
  have hupp' : incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) ≤
      dyadicMean (Fintype.card I) r (j-a) := by
    simpa [dyadicMean] using hupp
  rcases hx with hx | hx
  · have hc : (incidenceCount (pointedRegularIncidence C W haj hQW hW hgate) x : ℚ) ≤
        incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) := by
      nlinarith [hlow', hupp']
    rw [abs_of_nonpos (sub_nonpos.mpr hc)]
    nlinarith [hlow', hupp']
  · have hc : incidenceMean (pointedRegularIncidence C W haj hQW hW hgate) ≤
        (incidenceCount (pointedRegularIncidence C W haj hQW hW hgate) x : ℚ) := by
      nlinarith [hlow', hupp']
    rw [abs_of_nonneg (sub_nonneg.mpr hc)]
    nlinarith [hlow', hupp']

theorem pointed_badWindow_concentration {V I : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] [Fintype I] [Nonempty I]
    {a r j : Nat} {Q : Grass V a} [Nonempty (PointedQuery Q j)]
    (C : AdviceComplement Q) (W : I → Submodule (ZMod 2) V) (haj : a ≤ j)
    (hQW : ∀ i, Q.val ≤ W i) (hW : TwoGeneric W r)
    (hInj : Function.Injective W)
    (hgate : j-a ≤ Module.finrank (ZMod 2) C.A-2*r)
    (hspare : j-a+7 ≤ Module.finrank (ZMod 2) C.A-r) :
    eventMass (uniformLaw (PointedQuery Q j))
      (pointedBadWindowComplement r
        (pointedRegularIncidence C W haj hQW hW hgate)) ≤
      630 * (2 : ℚ)^(r*(j-a)) / Fintype.card I := by
  have hsub := pointed_badWindow_subset C W haj hQW hW hInj hgate hspare
  have hmass : eventMass (uniformLaw (PointedQuery Q j))
      (pointedBadWindowComplement r
        (pointedRegularIncidence C W haj hQW hW hgate)) ≤
      eventMass (uniformLaw (PointedQuery Q j))
        (relativeDeviationEvent
          (pointedRegularIncidence C W haj hQW hW hgate) (1/25)) := by
    unfold eventMass
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x hx hxnot
    exact (uniformLaw (PointedQuery Q j)).nonneg x
  have hcheb := pointed_rational_chebyshev C W haj hQW hW hInj hgate
    (by norm_num : (0 : ℚ) < 1/25)
  have hmean := pointed_dyadic_mean_bounds C W haj hQW hW hInj hgate hspare
  have hpos : 0 < incidenceMean
      (pointedRegularIncidence C W haj hQW hW hgate) :=
    incidenceMean_pos (pointedRegularIncidence C W haj hQW hW hgate)
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ eventMass (uniformLaw (PointedQuery Q j))
        (relativeDeviationEvent
          (pointedRegularIncidence C W haj hQW hW hgate) (1/25)) := hmass
    _ ≤ 1 / ((1/25 : ℚ)^2 * incidenceMean
        (pointedRegularIncidence C W haj hQW hW hgate)) := hcheb
    _ ≤ 630 * (2 : ℚ)^(r*(j-a)) / Fintype.card I := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hpos)).mpr
      have hlow := hmean.1
      have hp : 0 < (2 : ℚ)^(r*(j-a)) := by positivity
      have hlow' : (Fintype.card I : ℚ) * (127/128 : ℚ) /
          (2 : ℚ)^(r*(j-a)) ≤ incidenceMean
            (pointedRegularIncidence C W haj hQW hW hgate) := by
        convert hlow using 1 <;> ring
      have hcross : (Fintype.card I : ℚ) * (127/128 : ℚ) ≤
          (2 : ℚ)^(r*(j-a)) * incidenceMean
            (pointedRegularIncidence C W haj hQW hW hgate) :=
        by simpa [mul_assoc, mul_left_comm, mul_comm] using (div_le_iff₀ hp).mp hlow'
      have hbound : (Fintype.card I : ℚ) ≤
          ((2 : ℚ)^(r*(j-a)) * incidenceMean
            (pointedRegularIncidence C W haj hQW hW hgate)) / (127/128 : ℚ) :=
        (le_div_iff₀ (by norm_num : (0 : ℚ) < 127/128)).2 hcross
      have hcoef : (1 : ℚ) / (127/128) ≤ 630/625 := by norm_num
      have hscaled : (Fintype.card I : ℚ) ≤
          (630/625 : ℚ) * ((2 : ℚ)^(r*(j-a)) *
            incidenceMean (pointedRegularIncidence C W haj hQW hW hgate)) := by
        calc
          (Fintype.card I : ℚ) ≤
              ((2 : ℚ)^(r*(j-a)) * incidenceMean
                (pointedRegularIncidence C W haj hQW hW hgate)) / (127/128 : ℚ) := hbound
          _ = ((1 : ℚ) / (127/128)) *
              ((2 : ℚ)^(r*(j-a)) *
                incidenceMean (pointedRegularIncidence C W haj hQW hW hgate)) := by ring
          _ ≤ (630/625 : ℚ) * ((2 : ℚ)^(r*(j-a)) *
              incidenceMean (pointedRegularIncidence C W haj hQW hW hgate)) :=
                mul_le_mul_of_nonneg_right hcoef (by positivity)
      have hscaled' : (Fintype.card I : ℚ) ≤
          630 * (2 : ℚ)^(r*(j-a)) * ((1/25 : ℚ)^2 *
            incidenceMean (pointedRegularIncidence C W haj hQW hW hgate)) := by
        convert hscaled using 1 <;> norm_num <;> ring
      have htarget : 1 ≤ (630 * (2 : ℚ)^(r*(j-a)) *
          ((1/25 : ℚ)^2 * incidenceMean
            (pointedRegularIncidence C W haj hQW hW hgate))) / Fintype.card I := by
        apply (le_div_iff₀ hI).2
        simpa only [one_mul] using hscaled'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using htarget

end
end PvNP.RealizableHardness.ActualBinaryGrassmannSamplingBounds
