import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.MeanInequalities
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

/-! Finite probability-space inequalities for the actual append operator.

These lemmas concern the unconditional uniform matrix carriers.  In
particular, no rank-conditioned law or source-contract premise is introduced.
-/

namespace PvNP.RealizableHardness.ActualFiniteMomentLpBounds

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

set_option autoImplicit false
noncomputable section

/-- Finite Jensen on one genuine append fiber, with signed inputs handled by
absolute values. -/
theorem appendAverage_abs_pow_le {n c s p : Nat} (hp : 1 ≤ p)
    (F : BinaryMatrix n (c + s) → Real) (M : BinaryMatrix n c) :
    |appendAverage F M| ^ p ≤ appendAverage (fun W => |F W| ^ p) M := by
  let N : Real := Fintype.card (BinaryMatrix n s)
  have hN : 0 < N := by positivity
  have hsumabs : |∑ B : BinaryMatrix n s, F (appendBinaryMatrix M B)| ≤
      ∑ B : BinaryMatrix n s, |F (appendBinaryMatrix M B)| := Finset.abs_sum_le_sum_abs _ _
  have habsmean : |appendAverage F M| ≤ appendAverage (fun W => |F W|) M := by
    unfold appendAverage uniformMean
    change |(∑ B : BinaryMatrix n s, F (appendBinaryMatrix M B)) / N| ≤
      (∑ B : BinaryMatrix n s, |F (appendBinaryMatrix M B)|) / N
    rw [abs_div, abs_of_nonneg hN.le]
    exact div_le_div_of_nonneg_right hsumabs hN.le
  have hw' : ∑ B : BinaryMatrix n s, N⁻¹ = 1 := by
    simp [N, Finset.sum_const, nsmul_eq_mul]
  have hjensen := Real.pow_arith_mean_le_arith_mean_pow
    (Finset.univ : Finset (BinaryMatrix n s)) (fun _ => N⁻¹)
    (fun B => |F (appendBinaryMatrix M B)|)
    (by intro B hB; positivity) hw'
    (by intro B hB; positivity) p
  simp_rw [← Finset.mul_sum] at hjensen
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habsmean p
  calc
    |appendAverage F M| ^ p ≤ (appendAverage (fun W => |F W|) M) ^ p := hpow
    _ ≤ appendAverage (fun W => |F W| ^ p) M := by
      simpa [appendAverage, uniformMean, N, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc] using hjensen

/-- The unconditional appended operator contracts normalized finite p moments.
The right side is the moment on all matrices, not on a selected-rank carrier. -/
theorem appendAverage_lpMoment_le {n c s p : Nat} (hp : 1 ≤ p)
    (F : BinaryMatrix n (c + s) → Real) :
    lpMoment p (fun M => appendAverage F M) ≤ lpMoment p F := by
  unfold lpMoment
  have hpoint : ∀ M : BinaryMatrix n c,
      |appendAverage F M| ^ p ≤ appendAverage (fun W => |F W| ^ p) M :=
    fun M => appendAverage_abs_pow_le hp F M
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (BinaryMatrix n c)))
    (fun M _ => hpoint M)
  unfold uniformMean at *
  have hden : 0 < (Fintype.card (BinaryMatrix n c) : Real) := by positivity
  apply (div_le_div_of_nonneg_right hsum hden.le).trans_eq
  -- The two-stage uniform draw is exactly the uniform full-matrix draw.
  have hcard : Fintype.card (BinaryMatrix n (c + s)) =
      Fintype.card (BinaryMatrix n c) * Fintype.card (BinaryMatrix n s) := by
    calc
      Fintype.card (BinaryMatrix n (c + s)) = Fintype.card (BinaryMatrix n c × BinaryMatrix n s) :=
        (Fintype.card_congr (appendBinaryMatrixEquiv n c s)).symm
      _ = Fintype.card (BinaryMatrix n c) * Fintype.card (BinaryMatrix n s) :=
        Fintype.card_prod (BinaryMatrix n c) (BinaryMatrix n s)
  have hsum' : (∑ M : BinaryMatrix n c, ∑ B : BinaryMatrix n s,
      |F (appendBinaryMatrix M B)| ^ p) = ∑ W : BinaryMatrix n (c + s), |F W| ^ p := by
    calc
      _ = ∑ X : BinaryMatrix n c × BinaryMatrix n s,
          |F (appendBinaryMatrix X.1 X.2)| ^ p := by rw [← Fintype.sum_prod_type']
      _ = ∑ W : BinaryMatrix n (c + s), |F W| ^ p :=
        (appendBinaryMatrixEquiv n c s).sum_comp (fun W => |F W| ^ p)
  unfold appendAverage uniformMean
  rw [← Finset.sum_div, div_div, hsum', hcard, Nat.cast_mul]
  ring

/-- Rooted norm form of the finite-moment contraction.  `p ≥ 1` ensures the
real exponent `1/p` is nonnegative; the natural-number power stays explicit. -/
theorem appendAverage_lpNorm_le {n c s p : Nat} (hp : 1 ≤ p)
    (F : BinaryMatrix n (c + s) → Real) :
    lpNorm p (fun M => appendAverage F M) ≤ lpNorm p F := by
  unfold lpNorm
  have hmom := appendAverage_lpMoment_le hp F
  have hleft : 0 ≤ lpMoment p (fun M => appendAverage F M) := by
    unfold lpMoment uniformMean
    apply div_nonneg
    · exact Finset.sum_nonneg fun M _ => pow_nonneg (abs_nonneg _) p
    · positivity
  have hpow : 0 ≤ (1 / (p : Real)) := by positivity
  exact Real.rpow_le_rpow hleft hmom hpow

/-- Minkowski for the normalized uniform matrix measure.  The Mathlib finite
Minkowski theorem is first applied to raw sums; division by the positive
carrier size is then moved through the `1/p` real power. -/
theorem lpNorm_add_le {n d p : Nat} (hp : 1 ≤ p)
    (f g : BinaryMatrix n d → Real) :
    lpNorm p (fun W => f W + g W) ≤ lpNorm p f + lpNorm p g := by
  let N : Real := Fintype.card (BinaryMatrix n d)
  have hN : 0 < N := by positivity
  have hpR : 1 ≤ (p : Real) := by exact_mod_cast hp
  have hpPos : 0 < (p : Real) := by positivity
  have hraw := Real.Lp_add_le
    (s := (Finset.univ : Finset (BinaryMatrix n d)))
    (f := f) (g := g) (p := (p : Real)) hpR
  have hrawNat :
      (∑ W : BinaryMatrix n d, |f W + g W| ^ p) ^ (1 / (p : Real)) ≤
        (∑ W : BinaryMatrix n d, |f W| ^ p) ^ (1 / (p : Real)) +
          (∑ W : BinaryMatrix n d, |g W| ^ p) ^ (1 / (p : Real)) := by
    simpa only [Real.rpow_natCast] using hraw
  unfold lpNorm lpMoment uniformMean
  dsimp [N] at *
  have hdiv (x : Real) (hx : 0 ≤ x) :
      (x / (Fintype.card (BinaryMatrix n d) : Real)) ^ (1 / (p : Real)) =
        x ^ (1 / (p : Real)) /
          (Fintype.card (BinaryMatrix n d) : Real) ^ (1 / (p : Real)) := by
    rw [Real.div_rpow hx (by positivity) (1 / (p : Real))]
  have hsumf : 0 ≤ ∑ W : BinaryMatrix n d, |f W| ^ p :=
    Finset.sum_nonneg fun W _ => pow_nonneg (abs_nonneg _) p
  have hsumg : 0 ≤ ∑ W : BinaryMatrix n d, |g W| ^ p :=
    Finset.sum_nonneg fun W _ => pow_nonneg (abs_nonneg _) p
  have hsumfg : 0 ≤ ∑ W : BinaryMatrix n d, |f W + g W| ^ p :=
    Finset.sum_nonneg fun W _ => pow_nonneg (abs_nonneg _) p
  rw [hdiv _ hsumfg, hdiv _ hsumf, hdiv _ hsumg]
  have hden : 0 < (Fintype.card (BinaryMatrix n d) : Real) ^ (1 / (p : Real)) := by
    positivity
  simpa only [add_div] using (div_le_div_of_nonneg_right hrawNat hden.le)

/-- Minkowski over an arbitrary finite level family on the same normalized
uniform matrix carrier. -/
theorem finite_sum_lpNorm_le {n d p : Nat} (hp : 1 ≤ p)
    {α : Type*} (s : Finset α) (f : α → BinaryMatrix n d → Real) :
    lpNorm p (fun W => ∑ a ∈ s, f a W) ≤ ∑ a ∈ s, lpNorm p (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hpne : p ≠ 0 := by omega
      have hroot : (1 / (p : Real)) ≠ 0 := by positivity
      simp [lpNorm, lpMoment, uniformMean, hpne, hroot]
  | @insert a s ha ih =>
      have hfun : (fun W : BinaryMatrix n d => ∑ b ∈ insert a s, f b W) =
          (fun W => f a W + ∑ b ∈ s, f b W) := by
        funext W
        rw [Finset.sum_insert ha]
      rw [hfun, Finset.sum_insert ha]
      calc
        lpNorm p (fun W => f a W + ∑ b ∈ s, f b W) ≤
            lpNorm p (f a) + lpNorm p (fun W => ∑ b ∈ s, f b W) :=
          lpNorm_add_le hp (f a) (fun W => ∑ b ∈ s, f b W)
        _ ≤ lpNorm p (f a) + ∑ b ∈ s, lpNorm p (f b) := add_le_add le_rfl ih

/-- Normalized finite-level Minkowski inequality, ready for the low-rank sum
of rank projections. -/
theorem finiteLevel_lpNorm_sum_le {n d p : Nat} (hp : 1 ≤ p)
    {α : Type*} [Fintype α] (f : α → BinaryMatrix n d → Real) :
    lpNorm p (fun W => ∑ a : α, f a W) ≤ ∑ a : α, lpNorm p (f a) := by
  simpa using finite_sum_lpNorm_le hp Finset.univ f

/-- Aggregate finite-level moment bound, including the empty family.  This
cardinality factor is the finite Jensen cost for summing levels. -/
theorem finiteLevel_sum_abs_pow_le {n d : Nat} {α : Type*} [Fintype α]
    (p : Nat) (hp : 1 ≤ p) (f : α → BinaryMatrix n d → Real) (W : BinaryMatrix n d) :
    |∑ a : α, f a W| ^ p ≤
      (Fintype.card α : Real) ^ (p - 1) * ∑ a : α, |f a W| ^ p := by
  have hsumabs : |∑ a : α, f a W| ≤ ∑ a : α, |f a W| := Finset.abs_sum_le_sum_abs _ _
  have hsum := Real.rpow_sum_le_const_mul_sum_rpow
    (s := (Finset.univ : Finset α)) (f := fun a => f a W) (p := (p : Real))
    (by exact_mod_cast hp)
  have hpNat : 1 ≤ p := by exact_mod_cast hp
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hsumabs p
  calc
    |∑ a : α, f a W| ^ p ≤ (∑ a : α, |f a W|) ^ p := hpow
    _ = (∑ a : α, |f a W|) ^ (p : Real) := by rw [Real.rpow_natCast]
    _ ≤ (Fintype.card α : Real) ^ ((p : Real) - 1) *
        ∑ a : α, |f a W| ^ (p : Real) := hsum
    _ = (Fintype.card α : Real) ^ (p - 1) * ∑ a : α, |f a W| ^ p := by
      rw [show (p : Real) - 1 = ((p - 1 : Nat) : Real) by
        simpa only [Nat.cast_one] using (Nat.cast_sub (R := Real) hpNat).symm]
      simp only [Real.rpow_natCast]

/-- The same finite aggregate inequality after the matrix-space uniform mean.
This is the form used to collect per-level HC moment bounds; the empty level
family has both sides zero (with the natural `0 ^ 0` convention). -/
theorem finiteLevel_lpMoment_aggregate_le {n d : Nat} {α : Type*} [Fintype α]
    (p : Nat) (hp : 1 ≤ p) (f : α → BinaryMatrix n d → Real) :
    lpMoment p (fun W => ∑ a : α, f a W) ≤
      (Fintype.card α : Real) ^ (p - 1) * ∑ a : α, lpMoment p (f a) := by
  unfold lpMoment uniformMean
  have hpoint : ∀ W : BinaryMatrix n d,
      |∑ a : α, f a W| ^ p ≤
        (Fintype.card α : Real) ^ (p - 1) * ∑ a : α, |f a W| ^ p :=
    fun W => finiteLevel_sum_abs_pow_le p hp f W
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (BinaryMatrix n d)))
    (fun W _ => hpoint W)
  have hden : 0 < (Fintype.card (BinaryMatrix n d) : Real) := by positivity
  have hswap : (∑ W : BinaryMatrix n d, ∑ a : α, |f a W| ^ p) =
      ∑ a : α, ∑ W : BinaryMatrix n d, |f a W| ^ p := by
    rw [Finset.sum_comm]
  let C : Real := (Fintype.card α : Real) ^ (p - 1)
  have hscale :
      C * ∑ a : α,
          ((∑ W : BinaryMatrix n d, |f a W| ^ p) /
            (Fintype.card (BinaryMatrix n d) : Real)) =
        (∑ W : BinaryMatrix n d, C * ∑ a : α, |f a W| ^ p) /
          (Fintype.card (BinaryMatrix n d) : Real) := by
    calc
      _ = C * ((∑ a : α, ∑ W : BinaryMatrix n d, |f a W| ^ p) /
          (Fintype.card (BinaryMatrix n d) : Real)) := by rw [← Finset.sum_div]
      _ = C * ((∑ W : BinaryMatrix n d, ∑ a : α, |f a W| ^ p) /
          (Fintype.card (BinaryMatrix n d) : Real)) := by rw [hswap]
      _ = (∑ W : BinaryMatrix n d, C * ∑ a : α, |f a W| ^ p) /
          (Fintype.card (BinaryMatrix n d) : Real) := by
            rw [← mul_div_assoc, ← Finset.mul_sum]
  calc
    _ ≤ (∑ W : BinaryMatrix n d, C * ∑ a : α, |f a W| ^ p) /
        (Fintype.card (BinaryMatrix n d) : Real) :=
          div_le_div_of_nonneg_right hsum hden.le
    _ = C * ∑ a : α, lpMoment p (f a) := by
      unfold C lpMoment uniformMean
      exact hscale.symm

end
end PvNP.RealizableHardness.ActualFiniteMomentLpBounds
