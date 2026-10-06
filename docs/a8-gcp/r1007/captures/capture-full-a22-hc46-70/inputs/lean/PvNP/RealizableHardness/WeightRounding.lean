import PvNP.RealizableHardness.Formula
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log

/-! Exact finite upward rounding. This module does not assert computational hardness or runtime. -/
namespace PvNP.RealizableHardness.WeightRounding
open scoped BigOperators

def coordinate {V : Type*} (w : V → ℚ) (D : ℕ) (v : V) : ℕ := ⌈(D : ℚ) * w v⌉₊

def denominator {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) : ℕ :=
  ∑ v, coordinate w D v

def budgetNumerator {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ) : ℕ :=
  min (denominator w D) (⌈(D : ℚ) * t⌉₊ + Fintype.card V)

def roundedWeights {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (v : V) : ℚ :=
  (coordinate w D v : ℚ) / denominator w D

def roundedBudget {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ) : ℚ :=
  (budgetNumerator w D t : ℚ) / denominator w D

lemma coordinate_lower {V : Type*} (w : V → ℚ) (D : ℕ) (v : V) :
    (D : ℚ) * w v ≤ coordinate w D v := Nat.le_ceil _

lemma coordinate_upper {V : Type*} (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 ≤ w v) (v : V) :
    (coordinate w D v : ℚ) < (D : ℚ) * w v + 1 :=
  Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (hw v))

lemma coordinate_pos {V : Type*} (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 < w v) (hD : 0 < D) (v : V) : 0 < coordinate w D v := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (by exact_mod_cast hD) (hw v)

lemma denominator_cast {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) :
    (denominator w D : ℚ) = ∑ v, (coordinate w D v : ℚ) := by
  simp [denominator]

lemma raw_weight_lower {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ)
    (x : V → Bool) :
    (D : ℚ) * weight w x ≤ weight (fun v => (coordinate w D v : ℚ)) x := by
  unfold weight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  cases hx : x v <;> simp only [hx, Bool.false_eq_true, if_false, mul_zero, ite_true]
  · exact le_rfl
  · exact coordinate_lower w D v

lemma raw_weight_upper {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 ≤ w v) (x : V → Bool) :
    weight (fun v => (coordinate w D v : ℚ)) x ≤ (D : ℚ) * weight w x + Fintype.card V := by
  unfold weight
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ v, ((D : ℚ) * (if x v then w v else 0) + 1) := by
      apply Finset.sum_le_sum
      intro v _
      cases hx : x v
      · simp [hx]
      · simpa only [hx, ite_true] using (coordinate_upper w D hw v).le
    _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma raw_weight_le_denominator {V : Type*} [Fintype V]
    (w : V → ℚ) (D : ℕ) (x : V → Bool) :
    weight (fun v => (coordinate w D v : ℚ)) x ≤ denominator w D := by
  rw [denominator_cast]
  apply Finset.sum_le_sum
  intro v _
  split
  · exact le_rfl
  · positivity

theorem denominator_bounds {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1) :
    D ≤ denominator w D ∧ denominator w D ≤ D + Fintype.card V := by
  have hlo := raw_weight_lower w D (fun _ => true)
  have hhi := raw_weight_upper w D hw (fun _ => true)
  simp only [weight, ite_true, hnorm, mul_one, ← denominator_cast] at hlo hhi
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

lemma denominator_pos {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1) (hD : 0 < D) :
    0 < denominator w D := lt_of_lt_of_le hD (denominator_bounds w D hw hnorm).1

theorem roundedWeights_pos {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 < w v) (hnorm : ∑ v, w v = 1) (hD : 0 < D) :
    ∀ v, 0 < roundedWeights w D v := by
  intro v
  apply div_pos
  · exact_mod_cast coordinate_pos w D hw hD v
  · exact_mod_cast denominator_pos w D (fun v => (hw v).le) hnorm hD

theorem roundedWeights_sum {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1) (hD : 0 < D) :
    ∑ v, roundedWeights w D v = 1 := by
  unfold roundedWeights
  rw [← Finset.sum_div, ← denominator_cast]
  apply div_self
  exact_mod_cast (denominator_pos w D hw hnorm hD).ne'

theorem roundedBudget_valid {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1) (hD : 0 < D) (ht : 0 < t) :
    0 < roundedBudget w D t ∧ roundedBudget w D t ≤ 1 := by
  have hA := denominator_pos w D hw hnorm hD
  have hAq : (0 : ℚ) < denominator w D := by exact_mod_cast hA
  have hceil : 0 < ⌈(D : ℚ) * t⌉₊ := Nat.ceil_pos.mpr (mul_pos (by exact_mod_cast hD) ht)
  have hB : 0 < budgetNumerator w D t := by
    unfold budgetNumerator
    exact lt_min hA (lt_of_lt_of_le hceil (Nat.le_add_right _ _))
  constructor
  · exact div_pos (by exact_mod_cast hB) hAq
  · apply (div_le_one hAq).mpr
    exact_mod_cast (min_le_left (denominator w D) (⌈(D : ℚ) * t⌉₊ + Fintype.card V))

theorem rounding_complete {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ)
    (hw : ∀ v, 0 ≤ w v) (x : V → Bool) (hx : weight w x ≤ t) :
    weight (roundedWeights w D) x ≤ roundedBudget w D t := by
  change weight (fun v => (coordinate w D v : ℚ) / denominator w D) x ≤ _
  rw [weight_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hb := raw_weight_upper w D hw x
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg D : (0 : ℚ) ≤ D)
  have hc := Nat.le_ceil ((D : ℚ) * t)
  have hclip := raw_weight_le_denominator w D x
  change _ ≤ ((min (denominator w D) (⌈(D : ℚ) * t⌉₊ + Fintype.card V) : ℕ) : ℚ)
  rw [Nat.cast_min, Nat.cast_add]
  exact le_min hclip (by linarith)

lemma budgetNumerator_upper {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ)
    (ht : 0 ≤ t) :
    (budgetNumerator w D t : ℚ) ≤ (D : ℚ) * t + (Fintype.card V + 1) := by
  have hclip : budgetNumerator w D t ≤ ⌈(D : ℚ) * t⌉₊ + Fintype.card V := min_le_right _ _
  have hc := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg D : (0 : ℚ) ≤ D) ht)
  have hclipq : (budgetNumerator w D t : ℚ) ≤ (⌈(D : ℚ) * t⌉₊ : ℚ) + Fintype.card V := by
    exact_mod_cast hclip
  linarith

lemma budgetNumerator_div_bound {V : Type*} [Fintype V]
    (w : V → ℚ) (D : ℕ) (t : ℚ) (hD : 0 < D) (ht : 0 < t)
    (hlarge : 8 * ((Fintype.card V : ℚ) + 1) / t ≤ D) :
    (budgetNumerator w D t : ℚ) / D ≤ 9 * t / 8 := by
  have hlarge' := (div_le_iff₀ ht).mp hlarge
  have hupper := budgetNumerator_upper w D t ht.le
  apply (div_le_iff₀ (by exact_mod_cast hD : (0 : ℚ) < D)).mpr
  nlinarith

/-- Any assignment inside the rounded half-gap budget is inside the old gap budget. -/
theorem rounding_budget_transfer {V : Type*} [Fintype V]
    (w : V → ℚ) (D : ℕ) (t sig k : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1)
    (hD : 0 < D) (ht : 0 < t) (hsig : 0 < sig) (hk : 0 ≤ k) (hkle : k ≤ sig / 2)
    (hlarge : 8 * ((Fintype.card V : ℚ) + 1) / t ≤ D)
    (x : V → Bool) (hx : weight (roundedWeights w D) x ≤ k * roundedBudget w D t) :
    weight w x < sig * t := by
  have hAq : (0 : ℚ) < denominator w D := by
    exact_mod_cast denominator_pos w D hw hnorm hD
  change weight (fun v => (coordinate w D v : ℚ) / denominator w D) x ≤
    k * ((budgetNumerator w D t : ℚ) / denominator w D) at hx
  rw [weight_div] at hx
  have hraw : weight (fun v => (coordinate w D v : ℚ)) x ≤ k * budgetNumerator w D t := by
    have hx' : weight (fun v => (coordinate w D v : ℚ)) x / denominator w D ≤
        (k * budgetNumerator w D t) / denominator w D := by
      simpa only [mul_div_assoc] using hx
    exact (div_le_div_iff_of_pos_right hAq).mp hx'
  have hlo := raw_weight_lower w D x
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hold : weight w x ≤ k * ((budgetNumerator w D t : ℚ) / D) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hDq).mpr
    nlinarith only [hlo, hraw]
  have hfrac := budgetNumerator_div_bound w D t hD ht hlarge
  have hmid := mul_le_mul_of_nonneg_left hfrac hk
  have hlast := mul_le_mul_of_nonneg_right hkle (by positivity : 0 ≤ 9 * t / 8)
  have hprod := mul_pos hsig ht
  nlinarith

/-- Actual universal NO preservation, with the exact natural floor-half loss. -/
theorem rounding_sound {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℚ) (F : I → (V → Bool) → Bool) (D sig : ℕ) (t gam : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1)
    (hD : 0 < D) (ht : 0 < t) (hsig : 0 < sig)
    (hlarge : 8 * ((Fintype.card V : ℚ) + 1) / t ≤ D)
    (hno : ∀ x, weight w x ≤ (sig : ℚ) * t → average (fun i => F i x) < gam)
    (x : V → Bool)
    (hx : weight (roundedWeights w D) x ≤ ((sig / 2 : ℕ) : ℚ) * roundedBudget w D t) :
    average (fun i => F i x) < gam := by
  apply hno x
  exact (rounding_budget_transfer w D t sig (sig / 2 : ℕ) hw hnorm hD ht
    (by exact_mod_cast hsig) (by positivity) Nat.cast_div_le hlarge x hx).le

/-- Least power of two above the exact rational threshold, implemented via ceiling logarithm. -/
def dyadicScale (N : ℕ) (t : ℚ) : ℕ := 2 ^ Nat.clog 2 ⌈8 * ((N : ℚ) + 1) / t⌉₊

theorem dyadicScale_pos (N : ℕ) (t : ℚ) : 0 < dyadicScale N t := by
  unfold dyadicScale
  positivity

theorem dyadicScale_lower (N : ℕ) (t : ℚ) :
    8 * ((N : ℚ) + 1) / t ≤ dyadicScale N t := by
  unfold dyadicScale
  apply (Nat.le_ceil _).trans
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) ⌈8 * ((N : ℚ) + 1) / t⌉₊

theorem dyadicScale_least (N : ℕ) (t : ℚ) (j : ℕ)
    (hj : 8 * ((N : ℚ) + 1) / t ≤ ((2 ^ j : ℕ) : ℚ)) :
    dyadicScale N t ≤ 2 ^ j := by
  have hj' : ⌈8 * ((N : ℚ) + 1) / t⌉₊ ≤ 2 ^ j := Nat.ceil_le.mpr hj
  have he := (Nat.clog_le_iff_le_pow (by norm_num : 1 < (2 : ℕ))).mpr hj'
  exact Nat.pow_le_pow_right (by norm_num) he

theorem dyadicScale_upper (N : ℕ) (t : ℚ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (dyadicScale N t : ℚ) < 16 * ((N : ℚ) + 1) / t := by
  let q : ℚ := 8 * ((N : ℚ) + 1) / t
  have hq : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ ht).mpr
    have : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hc : 1 < ⌈q⌉₊ := Nat.lt_ceil.mpr (by simpa using hq)
  have he : 0 < Nat.clog 2 ⌈q⌉₊ := Nat.clog_pos (by norm_num) hc
  have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : ℕ)) hc
  have hpredq : ((2 ^ (Nat.clog 2 ⌈q⌉₊).pred : ℕ) : ℚ) < q := Nat.lt_ceil.mp hpred
  have hexp : Nat.clog 2 ⌈q⌉₊ = (Nat.clog 2 ⌈q⌉₊).pred + 1 :=
    (Nat.succ_pred_eq_of_pos he).symm
  change ((2 ^ Nat.clog 2 ⌈q⌉₊ : ℕ) : ℚ) < _
  rw [hexp, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ < q * 2 := mul_lt_mul_of_pos_right hpredq (by norm_num)
    _ = _ := by dsimp [q]; ring

/-- Explicit natural common denominator and integer numerators, including clipped budget. -/
theorem common_denominator {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ)
    (hw : ∀ v, 0 < w v) (hnorm : ∑ v, w v = 1) (hD : 0 < D) (ht : 0 < t) :
    (0 < denominator w D) ∧
    (∀ v, 0 < coordinate w D v ∧ coordinate w D v ≤ denominator w D ∧
      roundedWeights w D v * denominator w D = (coordinate w D v : ℚ)) ∧
    (0 < budgetNumerator w D t ∧ budgetNumerator w D t ≤ denominator w D ∧
      roundedBudget w D t * denominator w D = (budgetNumerator w D t : ℚ)) := by
  have hA := denominator_pos w D (fun v => (hw v).le) hnorm hD
  have hAq : (denominator w D : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  refine ⟨hA, ?_, ?_⟩
  · intro v
    refine ⟨coordinate_pos w D hw hD v, ?_, ?_⟩
    · exact Finset.single_le_sum (fun i _ => Nat.zero_le (coordinate w D i)) (Finset.mem_univ v)
    · exact div_mul_cancel₀ _ hAq
  · have hceil : 0 < ⌈(D : ℚ) * t⌉₊ := Nat.ceil_pos.mpr (mul_pos (by exact_mod_cast hD) ht)
    refine ⟨lt_min hA (lt_of_lt_of_le hceil (Nat.le_add_right _ _)), min_le_left _ _, ?_⟩
    exact div_mul_cancel₀ _ hAq

/-- Multiples of A give actual integral coordinate and budget lengths. -/
theorem integral_lengths {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ)
    (hA : 0 < denominator w D) (m : ℕ) :
    (∀ v, roundedWeights w D v * ((m * denominator w D : ℕ) : ℚ) =
      ((m * coordinate w D v : ℕ) : ℚ)) ∧
    roundedBudget w D t * ((m * denominator w D : ℕ) : ℚ) =
      ((m * budgetNumerator w D t : ℕ) : ℚ) := by
  have hAq : (denominator w D : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  constructor
  · intro v
    unfold roundedWeights
    push_cast
    field_simp
  · unfold roundedBudget
    push_cast
    field_simp

/-- The exact dyadic construction has an explicit numeric common-denominator bound. -/
theorem dyadic_denominator_bound {V : Type*} [Fintype V] (w : V → ℚ) (t : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    (denominator w (dyadicScale (Fintype.card V) t) : ℚ) <
      16 * ((Fintype.card V : ℚ) + 1) / t + Fintype.card V := by
  have hA := (denominator_bounds w (dyadicScale (Fintype.card V) t) hw hnorm).2
  have hAq : (denominator w (dyadicScale (Fintype.card V) t) : ℚ) ≤
      (dyadicScale (Fintype.card V) t : ℚ) + Fintype.card V := by exact_mod_cast hA
  have hD := dyadicScale_upper (Fintype.card V) t ht ht1
  linarith

/-- An upper bound on reciprocal budget becomes a natural numeric denominator bound. -/
theorem denominator_bound_of_inverse_budget {V : Type*} [Fintype V]
    (w : V → ℚ) (t : ℚ) (P : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hInv : 1 / t ≤ (P : ℚ)) :
    denominator w (dyadicScale (Fintype.card V) t) ≤
      16 * (Fintype.card V + 1) * P + Fintype.card V := by
  have hbound := dyadic_denominator_bound w t hw hnorm ht ht1
  have hmul := mul_le_mul_of_nonneg_left hInv
    (by positivity : (0 : ℚ) ≤ 16 * ((Fintype.card V : ℚ) + 1))
  have hA : (denominator w (dyadicScale (Fintype.card V) t) : ℚ) ≤
      16 * ((Fintype.card V : ℚ) + 1) * P + Fintype.card V := by
    rw [mul_one_div] at hmul
    linarith
  exact_mod_cast hA

/-- A concrete polynomial numeric bound follows from a polynomial reciprocal-budget bound. -/
theorem polynomial_denominator_bound {V : Type*} [Fintype V]
    (w : V → ℚ) (t : ℚ) (n k : ℕ)
    (hw : ∀ v, 0 ≤ w v) (hnorm : ∑ v, w v = 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hN : Fintype.card V ≤ n)
    (hInv : 1 / t ≤ ((n + 1 : ℕ) : ℚ) ^ k) :
    denominator w (dyadicScale (Fintype.card V) t) ≤ 17 * (n + 1) ^ (k + 1) := by
  have hInv' : 1 / t ≤ (((n + 1) ^ k : ℕ) : ℚ) := by exact_mod_cast hInv
  have hA := denominator_bound_of_inverse_budget w t ((n + 1) ^ k) hw hnorm ht ht1 hInv'
  have hP : 0 < (n + 1) ^ k := pow_pos (by omega) _
  calc
    _ ≤ 16 * (Fintype.card V + 1) * (n + 1) ^ k + Fintype.card V := hA
    _ ≤ 16 * (n + 1) * (n + 1) ^ k + n := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hN 1))) hN
    _ ≤ 17 * (n + 1) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hP)]

/-- Positive integral numerators give explicit inverse-denominator lower bounds. -/
theorem rounded_lower_bounds {V : Type*} [Fintype V] (w : V → ℚ) (D : ℕ) (t : ℚ)
    (hw : ∀ v, 0 < w v) (hnorm : ∑ v, w v = 1) (hD : 0 < D) (ht : 0 < t) :
    (∀ v, 1 / (denominator w D : ℚ) ≤ roundedWeights w D v) ∧
    1 / (denominator w D : ℚ) ≤ roundedBudget w D t := by
  have h := common_denominator w D t hw hnorm hD ht
  constructor
  · intro v
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (Nat.succ_le_of_lt (h.2.1 v).1)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (Nat.succ_le_of_lt h.2.2.1)

/-- The dyadic rounding lemma for actual formulas; the indexed formulas are unchanged. -/
theorem formula_rounding {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℚ) (F : I → Formula V) (t gam : ℚ) (sig : ℕ)
    (hw : ∀ v, 0 < w v) (hnorm : ∑ v, w v = 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hsig : 0 < sig) :
    let D := dyadicScale (Fintype.card V) t
    (∀ v, 0 < roundedWeights w D v) ∧ (∑ v, roundedWeights w D v = 1) ∧
    (0 < roundedBudget w D t ∧ roundedBudget w D t ≤ 1) ∧
    ((denominator w D : ℚ) < 16 * ((Fintype.card V : ℚ) + 1) / t + Fintype.card V) ∧
    (∀ x, weight w x ≤ t → weight (roundedWeights w D) x ≤ roundedBudget w D t) ∧
    ((∀ x, weight w x ≤ (sig : ℚ) * t → average (fun i => Formula.eval x (F i)) < gam) →
      ∀ x, weight (roundedWeights w D) x ≤ ((sig / 2 : ℕ) : ℚ) * roundedBudget w D t →
        average (fun i => Formula.eval x (F i)) < gam) := by
  dsimp only
  have hD := dyadicScale_pos (Fintype.card V) t
  have hwn := fun v => (hw v).le
  refine ⟨roundedWeights_pos w _ hw hnorm hD, roundedWeights_sum w _ hwn hnorm hD,
    roundedBudget_valid w _ t hwn hnorm hD ht,
    dyadic_denominator_bound w t hwn hnorm ht ht1, ?_, ?_⟩
  · intro x hx
    exact rounding_complete w _ t hwn x hx
  · intro hno x hx
    exact rounding_sound w (fun i x => Formula.eval x (F i)) _ sig t gam hwn hnorm hD ht
      hsig (dyadicScale_lower _ t) hno x hx

end PvNP.RealizableHardness.WeightRounding
