import Mathlib.Analysis.MeanInequalities
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A21DyadicMoment

/-! Finite normalized complex norms with real exponents. These are the actual
probability norms needed by original A22, including its nonintegral conjugate
exponent. This module introduces no globalness or influence oracle. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46RealQNorm
open BinaryMatrixFourier
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The real conjugate exponent, with no integer rounding. -/
def pConjugate (p : Nat) : Real := (p : Real) / ((p : Real) - 1)

/-- The normalized real-exponent complex norm on a finite carrier. -/
def realQNorm {X : Type*} [Fintype X] (q : Real) (f : X → Complex) : Real :=
  ((∑ x, ‖f x‖ ^ q) / (Fintype.card X : Real)) ^ (1 / q)

/-- Explicit normalization separates the cardinal root from the raw norm. -/
theorem realQNorm_eq_div {X : Type*} [Fintype X] (q : Real) (f : X → Complex) :
    realQNorm q f = (∑ x, ‖f x‖ ^ q) ^ (1 / q) /
      (Fintype.card X : Real) ^ (1 / q) := by
  exact Real.div_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Nat.cast_nonneg _) _

theorem realQNorm_nonneg {X : Type*} [Fintype X] (q : Real) (f : X → Complex) :
    0 ≤ realQNorm q f := Real.rpow_nonneg (div_nonneg
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)) _

/-- Norm reindexing has no cardinal loss. -/
theorem realQNorm_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (q : Real) (f : Y → Complex) :
    realQNorm q (fun x => f (e x)) = realQNorm q f := by
  unfold realQNorm
  rw [Equiv.sum_comp e (fun y => ‖f y‖ ^ q), Fintype.card_congr e]

/-- Pointwise norm domination implies domination of every positive-exponent norm. -/
theorem realQNorm_mono {X : Type*} [Fintype X] {q : Real} (hq : 0 < q)
    (f g : X → Complex) (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    realQNorm q f ≤ realQNorm q g := by
  apply Real.rpow_le_rpow
  · exact div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum fun x _ => Real.rpow_le_rpow (norm_nonneg _) (h x) hq.le
  · exact div_nonneg (by norm_num) hq.le

/-- Real-exponent Minkowski for normalized complex functions. -/
theorem realQNorm_add_le {X : Type*} [Fintype X] {q : Real} (hq : 1 ≤ q)
    (f g : X → Complex) :
    realQNorm q (fun x => f x + g x) ≤ realQNorm q f + realQNorm q g := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hr := Real.Lp_add_le_of_nonneg (s := (Finset.univ : Finset X))
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖) hq
    (fun x _ => norm_nonneg _) (fun x _ => norm_nonneg _)
  have ht : (∑ x, ‖f x + g x‖ ^ q) ^ (1 / q) ≤
      (∑ x, (‖f x‖ + ‖g x‖) ^ q) ^ (1 / q) := by
    apply Real.rpow_le_rpow
    · exact Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _
    · exact Finset.sum_le_sum fun x _ => Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hq0.le
    · exact div_nonneg (by norm_num) hq0.le
  rw [realQNorm_eq_div, realQNorm_eq_div, realQNorm_eq_div, ← add_div]
  exact div_le_div_of_nonneg_right (ht.trans hr) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Finite normalized complex Holder: conjugacy cancels the entire cardinality. -/
theorem realQNorm_holder {X : Type*} [Fintype X] [Nonempty X]
    {p q : Real} (hpq : p.HolderConjugate q) (f g : X → Complex) :
    ‖(∑ x, star (f x) * g x) / (Fintype.card X : Complex)‖ ≤
      realQNorm p f * realQNorm q g := by
  let N : Real := Fintype.card X
  have hN : 0 < N := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)
  have hr := Real.inner_le_Lp_mul_Lq_of_nonneg (s := (Finset.univ : Finset X))
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖) hpq
    (fun x _ => norm_nonneg _) (fun x _ => norm_nonneg _)
  have ht : ‖∑ x, star (f x) * g x‖ ≤ ∑ x, ‖f x‖ * ‖g x‖ := by
    exact (norm_sum_le _ _).trans (by simp only [norm_mul, norm_star]; exact le_rfl)
  have hcancel : N ^ (1 / p) * N ^ (1 / q) = N := by
    rw [← Real.rpow_add hN]
    have he : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
    rw [he, Real.rpow_one]
  rw [norm_div]
  have hcardNorm : ‖(Fintype.card X : Complex)‖ = N := by
    simp [N]
  rw [hcardNorm, realQNorm_eq_div, realQNorm_eq_div, div_mul_div_comm, hcancel]
  exact div_le_div_of_nonneg_right (ht.trans hr) hN.le


/-- The exact real conjugate is greater than one for the dyadic moment range. -/
theorem pConjugate_holder {p : Nat} (hp : 2 ≤ p) :
    (p : Real).HolderConjugate (pConjugate p) := by
  exact Real.HolderConjugate.conjExponent (by exact_mod_cast (by omega : 1 < p))

/-- Taking a natural positive power recovers the normalized moment exactly. -/
theorem realQNorm_nat_pow {X : Type*} [Fintype X] {p : Nat} (hp : 0 < p)
    (f : X → Complex) :
    realQNorm (p : Real) f ^ p =
      (∑ x, ‖f x‖ ^ p) / (Fintype.card X : Real) := by
  unfold realQNorm
  simp only [Real.rpow_natCast]
  rw [one_div, Real.rpow_inv_natCast_pow
    (div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)) hp.ne']

/-- The generic real norm agrees with the manuscript norm on matrix space. -/
theorem realQNorm_nat_eq_lpNorm {n d p : Nat} (f : BinaryMatrix n d → Complex) :
    realQNorm (p : Real) f = BinaryMatrixFourier.lpNorm p (fun x => ‖f x‖) := by
  simp [realQNorm, BinaryMatrixFourier.lpNorm, BinaryMatrixFourier.lpMoment,
    BinaryMatrixFourier.uniformMean, Real.rpow_natCast, abs_of_nonneg (norm_nonneg _)]

/-- Natural-powered Holder, keeping the conjugate norm a true real-q norm. -/
theorem realQNorm_holder_nat_pow {X : Type*} [Fintype X] [Nonempty X]
    {p : Nat} (hp : 2 ≤ p) (f g : X → Complex) :
    ‖(∑ x, star (f x) * g x) / (Fintype.card X : Complex)‖ ^ p ≤
      ((∑ x, ‖f x‖ ^ p) / (Fintype.card X : Real)) *
        realQNorm (pConjugate p) g ^ p := by
  have ht := pow_le_pow_left₀ (norm_nonneg _)
    (realQNorm_holder (pConjugate_holder hp) f g) p
  rw [mul_pow, realQNorm_nat_pow (by omega : 0 < p)] at ht
  exact ht

/-- Scalar homogeneity for a genuine positive real exponent. -/
theorem realQNorm_mul {X : Type*} [Fintype X] {q : Real} (hq : 0 < q)
    (c : Complex) (f : X → Complex) :
    realQNorm q (fun x => c * f x) = ‖c‖ * realQNorm q f := by
  have hs : (∑ x, ‖c * f x‖ ^ q) = ‖c‖ ^ q * ∑ x, ‖f x‖ ^ q := by
    simp_rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [Finset.mul_sum]
  rw [realQNorm_eq_div, hs,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)]
  have he : q * (1 / q) = 1 := by field_simp [hq.ne']
  rw [he, Real.rpow_one, realQNorm_eq_div]
  ring

/-- A finite sum costs exactly the sum of the individual norms. -/
theorem realQNorm_finset_sum_le {X I : Type*} [Fintype X] {q : Real}
    (hq : 1 ≤ q) (s : Finset I) (f : I → X → Complex) :
    realQNorm q (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, realQNorm q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
      have hz : (0 : Real) ^ (1 / q) = 0 :=
        Real.zero_rpow (div_ne_zero one_ne_zero hq0.ne')
      simpa only [realQNorm, Finset.sum_empty, norm_zero,
        Real.zero_rpow hq0.ne', Finset.sum_const_zero, zero_div] using le_of_eq hz
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (realQNorm_add_le hq (f i) (fun x => ∑ j ∈ s, f j x)).trans
        (add_le_add le_rfl ih)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46RealQNorm
