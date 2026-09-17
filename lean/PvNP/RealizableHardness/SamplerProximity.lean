/- UNCOMPILED source draft; no kernel acceptance is asserted. -/
import PvNP.RealizableHardness.SamplerParameters
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PvNP.RealizableHardness.SamplerProximity
noncomputable section
open Filter SamplerParameters DropTailParameters

def exponent (A h : ℕ) : ℝ := (2 ^ (A * h ^ 2) : ℕ)
def mean (A h : ℕ) : ℝ := (A : ℝ) * (h : ℝ) ^ 2
def two (x : ℝ) : ℝ := (2 : ℝ) ^ x

lemma two_pos (x : ℝ) : 0 < two x := Real.rpow_pos_of_pos (by norm_num) _
lemma two_mono {x y : ℝ} (h : x ≤ y) : two x ≤ two y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h
lemma two_add (x y : ℝ) : two (x + y) = two x * two y :=
  Real.rpow_add (by norm_num) _ _
lemma two_nat (n : ℕ) : two (n : ℝ) = (2 : ℝ) ^ n := Real.rpow_natCast _ _
lemma blocks_real (A h : ℕ) : (blocks A h : ℝ) = two (exponent A h) := by
  unfold blocks exponent two
  rw [Real.rpow_natCast]
  norm_cast
lemma beta_real (A h : ℕ) : (beta A h : ℝ) = mean A h / two (exponent A h) := by
  simp [beta, mean, blocks_real, Rat.cast_div, Rat.cast_natCast]
lemma decay_two (k h : ℕ) : decay k h = two (-(k : ℝ) * (h : ℝ) ^ 2) := by
  rw [decay_eq_reciprocal]
  have he : -(k : ℝ) * (h : ℝ) ^ 2 = -((k * h ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  unfold two
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp only [one_div]

/-- Polynomial growth is dominated by the actual inner exponent. -/
theorem eventual_inner_domination (A : ℕ) (hA : 0 < A) (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → C * (h : ℝ) ^ 4 ≤ exponent A h := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 4 (show (1 : ℝ) < 2 by norm_num)
  have he : ∀ᶠ h : ℕ in atTop, (h : ℝ) ^ 4 / (2 : ℝ) ^ h < 1 / C :=
    ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / C))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨max N 1, ?_⟩
  intro h hh
  have hh1 : 1 ≤ h := le_trans (le_max_right _ _) hh
  have hn := hN h (le_trans (le_max_left _ _) hh)
  have hb : C * (h : ℝ) ^ 4 ≤ (2 : ℝ) ^ h := by
    have := (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) h)).1 hn
    have := (lt_div_iff₀ hC).1 (show (h : ℝ) ^ 4 < (2 : ℝ) ^ h / C by
      simpa [div_eq_mul_inv, mul_comm] using this)
    nlinarith
  have hs : h ≤ A * h ^ 2 := by
    have ha : 1 ≤ A := hA
    have hm := Nat.mul_le_mul_left (h ^ 2) ha
    nlinarith
  exact hb.trans (by
    unfold exponent
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hs)

/-- A convenient sufficient budget; the eventual theorem below proves it. -/
def Ready (A r h : ℕ) : Prop := 1 ≤ h ∧
  mean A h + 2 * (r : ℝ) * (h : ℝ) ^ 4 + ((r : ℝ) + 200) * (h : ℝ) ^ 2 +
    2 * (h : ℝ) + (r : ℝ) + 10 ≤ exponent A h / 4

theorem eventually_ready (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h → Ready A r h := by
  obtain ⟨N, hN⟩ := eventual_inner_domination A hA
    (4 * ((A : ℝ) + 4 * (r : ℝ) + 212)) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro h hh
  have hh1 : 1 ≤ h := le_trans (le_max_right _ _) hh
  have hx : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have h2 : (h : ℝ) ^ 2 ≤ (h : ℝ) ^ 4 := by nlinarith [sq_nonneg ((h : ℝ) ^ 2 - 1)]
  have h4 : (1 : ℝ) ≤ (h : ℝ) ^ 4 := by nlinarith
  have h14 : (h : ℝ) ≤ (h : ℝ) ^ 4 := by nlinarith
  have hA2 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
  have hr2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (r : ℝ) + 200 by positivity)
  have hr4 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (r : ℝ) + 10 by positivity)
  have hb := hN h (le_trans (le_max_left _ _) hh)
  refine ⟨hh1, ?_⟩
  unfold mean
  nlinarith

lemma mean_le_two (A h : ℕ) : mean A h ≤ two (mean A h) := by
  have hn : A * h ^ 2 ≤ 2 ^ (A * h ^ 2) := Nat.le_of_lt Nat.lt_two_pow_self
  have hc : mean A h = ((A * h ^ 2 : ℕ) : ℝ) := by simp [mean]
  rw [hc, two_nat]
  exact_mod_cast hn

lemma beta_le_two (A h : ℕ) : (beta A h : ℝ) ≤ two (mean A h - exponent A h) := by
  rw [beta_real]
  unfold two
  rw [Real.rpow_sub (by norm_num)]
  exact div_le_div_of_nonneg_right (mean_le_two A h) (two_pos _).le

lemma advice_le_two (A h a : ℕ) :
    (beta A h : ℝ) * Real.sqrt (blocks A h : ℝ) * (2 : ℝ) ^ (a + 4) ≤
      two (mean A h - exponent A h / 2 + (a : ℝ) + 4) := by
  have hs : Real.sqrt (blocks A h : ℝ) = two (exponent A h / 2) := by
    rw [blocks_real, Real.sqrt_eq_rpow]
    unfold two
    rw [← Real.rpow_mul (by norm_num)]
    congr 1 <;> ring
  rw [hs, ← two_nat]
  have ht := mul_le_mul_of_nonneg_right (beta_le_two A h) (two_pos (exponent A h / 2)).le
  have hu := mul_le_mul_of_nonneg_right ht (two_pos ((a + 4 : ℕ) : ℝ)).le
  have he : two (mean A h - exponent A h) * two (exponent A h / 2) * two ((a + 4 : ℕ) : ℝ) =
      two (mean A h - exponent A h / 2 + (a : ℝ) + 4) := by
    rw [← two_add, ← two_add]
    congr 1
    push_cast
    ring
  rw [he] at hu
  exact hu

lemma zoom_le_two (A h : ℕ) :
    Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) ≤
      two (mean A h / 2 - exponent A h / 4) := by
  have hb : (0 : ℝ) ≤ beta A h := by exact_mod_cast beta_nonneg A h
  have hs := Real.rpow_le_rpow hb (beta_le_two A h) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [Real.sqrt_eq_rpow, blocks_real]
  have ht := mul_le_mul_of_nonneg_right hs
    (Real.rpow_nonneg (two_pos (exponent A h)).le (1 / 4 : ℝ))
  have he : two (mean A h - exponent A h) ^ (1 / 2 : ℝ) *
      two (exponent A h) ^ (1 / 4 : ℝ) = two (mean A h / 2 - exponent A h / 4) := by
    unfold two
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1 <;> ring
  rw [he] at ht
  exact ht

lemma ready_advice {A r h a : ℕ} (hr : Ready A r h) (ha : a ≤ r) :
    (beta A h : ℝ) * Real.sqrt (blocks A h : ℝ) * (2 : ℝ) ^ (a + 4) ≤ decay 100 h := by
  apply (advice_le_two A h a).trans
  rw [decay_two]
  apply two_mono
  have hac : (a : ℝ) ≤ r := by exact_mod_cast ha
  have hn : 0 ≤ mean A h := by unfold mean; positivity
  have he : 0 ≤ exponent A h := by unfold exponent; positivity
  have hx : (1 : ℝ) ≤ h := by exact_mod_cast hr.1
  have hp : 0 ≤ 2 * (r : ℝ) * (h : ℝ) ^ 4 := by positivity
  nlinarith [hr.2, sq_nonneg ((h : ℝ) - 1)]

lemma ready_zoom_scaled {A r h : ℕ} (hr : Ready A r h) :
    Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) *
      (2 : ℝ) ^ (2 * h + 5) ≤ decay 100 h := by
  have ht := mul_le_mul_of_nonneg_right (zoom_le_two A h)
    (show (0 : ℝ) ≤ 2 ^ (2 * h + 5) by positivity)
  apply ht.trans
  rw [← two_nat, ← two_add, decay_two]
  apply two_mono
  have hn : 0 ≤ mean A h := by unfold mean; positivity
  have hp : 0 ≤ 2 * (r : ℝ) * (h : ℝ) ^ 4 := by positivity
  have hq : 0 ≤ (r : ℝ) * (h : ℝ) ^ 2 := by positivity
  push_cast
  nlinarith [hr.2]

lemma ready_zoom {A r h : ℕ} (hr : Ready A r h) :
    Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) ≤ decay 100 h := by
  have ht := ready_zoom_scaled hr
  have hp : (1 : ℝ) ≤ 2 ^ (2 * h + 5) := one_le_pow₀ (by norm_num)
  have hn : 0 ≤ Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) := by positivity
  nlinarith

lemma ready_small_beta {A r h : ℕ} (hr : Ready A r h) :
    (2 : ℝ) ^ (2 * h) * (beta A h : ℝ) ≤ 1 / 8 := by
  have ht := mul_le_mul_of_nonneg_left (beta_le_two A h)
    (show (0 : ℝ) ≤ 2 ^ (2 * h) by positivity)
  apply ht.trans
  rw [← two_nat, ← two_add]
  have hb : two (((2 * h : ℕ) : ℝ) + (mean A h - exponent A h)) ≤ two (-3) := by
    apply two_mono
    have hp : 0 ≤ 2 * (r : ℝ) * (h : ℝ) ^ 4 := by positivity
    have hq : 0 ≤ ((r : ℝ) + 200) * (h : ℝ) ^ 2 := by positivity
    have he : 0 ≤ exponent A h := by unfold exponent; positivity
    push_cast
    nlinarith [hr.2]
  have he : two (-3) = (1 : ℝ) / 8 := by
    change (2 : ℝ) ^ (-(3 : ℝ)) = _
    rw [Real.rpow_neg (by norm_num)]
    norm_num
  rw [he] at hb
  exact hb

lemma ready_density {A r h a c : ℕ} (hr : Ready A r h) (ha : a ≤ r) (hc : c ≤ r) :
    8 * (2 : ℝ) ^ (2 * a * h ^ 4) * ((2 : ℝ) ^ c - 1) * (beta A h : ℝ) ≤ decay 30 h := by
  have hb : (0 : ℝ) ≤ beta A h := by exact_mod_cast beta_nonneg A h
  have ht : 8 * (2 : ℝ) ^ (2 * a * h ^ 4) * ((2 : ℝ) ^ c - 1) * (beta A h : ℝ) ≤
      (2 : ℝ) ^ 3 * (2 : ℝ) ^ (2 * a * h ^ 4) * (2 : ℝ) ^ c * two (mean A h - exponent A h) := by
    calc
      _ ≤ 8 * (2 : ℝ) ^ (2 * a * h ^ 4) * (2 : ℝ) ^ c * (beta A h : ℝ) := by gcongr; linarith
      _ ≤ _ := by norm_num; gcongr; exact beta_le_two A h
  apply ht.trans
  rw [← two_nat 3, ← two_nat (2 * a * h ^ 4), ← two_nat c, ← two_add, ← two_add, ← two_add, decay_two]
  apply two_mono
  have hac : (a : ℝ) ≤ r := by exact_mod_cast ha
  have hcc : (c : ℝ) ≤ r := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hac (show 0 ≤ 2 * (h : ℝ) ^ 4 by positivity)
  have he : 0 ≤ exponent A h := by unfold exponent; positivity
  have hq : 0 ≤ (r : ℝ) * (h : ℝ) ^ 2 := by positivity
  push_cast
  nlinarith [hr.2]

lemma ready_dimensions {A r h : ℕ} (hr : Ready A r h) :
    r + 1 ≤ blocks A h ∧ 2 * h ≤ blocks A h := by
  have hE : exponent A h ≤ (blocks A h : ℝ) := by
    have hn : 2 ^ (A * h ^ 2) ≤ blocks A h := Nat.le_of_lt Nat.lt_two_pow_self
    unfold exponent
    exact_mod_cast hn
  have hn : 0 ≤ mean A h := by unfold mean; positivity
  have hp : 0 ≤ 2 * (r : ℝ) * (h : ℝ) ^ 4 := by positivity
  have hq : 0 ≤ ((r : ℝ) + 200) * (h : ℝ) ^ 2 := by positivity
  constructor
  · have : (r : ℝ) + 1 ≤ (blocks A h : ℝ) := by nlinarith [hr.2]
    exact_mod_cast this
  · have : 2 * (h : ℝ) ≤ (blocks A h : ℝ) := by nlinarith [hr.2]
    exact_mod_cast this

lemma decay_antitone {k l h : ℕ} (hkl : k ≤ l) : decay l h ≤ decay k h := by
  unfold decay
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_right _ hkl)

lemma five_decay70_lt {h : ℕ} (hh : 1 ≤ h) : 5 * decay 70 h < decay 20 h := by
  have hp : 0 < decay 20 h := decay_pos 20 h
  have hs : decay 50 h ≤ (1 / 2 : ℝ) ^ 3 := by
    unfold decay
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    have : 1 ≤ h ^ 2 := one_le_pow₀ hh
    omega
  have he : decay 70 h = decay 20 h * decay 50 h := by
    simpa using decay_add 20 50 h
  rw [he]
  norm_num at hs
  nlinarith

lemma ready_exceptional {A r h a : ℕ} (hr : Ready A r h) (ha : a ≤ r) :
    Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) +
      3 * ((beta A h : ℝ) * Real.sqrt (blocks A h : ℝ) * (2 : ℝ) ^ (a + 4)) +
      decay 70 h < decay 20 h := by
  have hz := ready_zoom hr
  have hd := ready_advice hr ha
  have hm : decay 100 h ≤ decay 70 h := decay_antitone (by norm_num)
  have he := five_decay70_lt hr.1
  linarith

/-- One threshold, chosen after A and r, works for every later h and every
bounded advice dimension and codimension. The sampler is the prescribed family. -/
theorem eventual_proximity (A r : ℕ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ h : ℕ, N ≤ h →
      r + 1 ≤ blocks A h ∧ 2 * h ≤ blocks A h ∧
      Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) ≤ decay 100 h ∧
      Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) *
        (2 : ℝ) ^ (2 * h + 5) ≤ decay 100 h ∧
      (2 : ℝ) ^ (2 * h) * (beta A h : ℝ) ≤ 1 / 8 ∧
      ∀ a c : ℕ, a ≤ r → c ≤ r →
        (beta A h : ℝ) * Real.sqrt (blocks A h : ℝ) * (2 : ℝ) ^ (a + 4) ≤ decay 100 h ∧
        8 * (2 : ℝ) ^ (2 * a * h ^ 4) * ((2 : ℝ) ^ c - 1) * (beta A h : ℝ) ≤ decay 30 h ∧
        Real.sqrt (beta A h : ℝ) * (blocks A h : ℝ) ^ (1 / 4 : ℝ) +
          3 * ((beta A h : ℝ) * Real.sqrt (blocks A h : ℝ) * (2 : ℝ) ^ (a + 4)) +
          decay 70 h < decay 20 h := by
  obtain ⟨N, hN⟩ := eventually_ready A r hA
  refine ⟨N, ?_⟩
  intro h hh
  have hr := hN h hh
  exact ⟨(ready_dimensions hr).1, (ready_dimensions hr).2, ready_zoom hr,
    ready_zoom_scaled hr, ready_small_beta hr, fun a c ha hc =>
      ⟨ready_advice hr ha, ready_density hr ha hc, ready_exceptional hr ha⟩⟩

end
end PvNP.RealizableHardness.SamplerProximity
