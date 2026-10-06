import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

/-! Exact scalar absorption estimates used by the outer A18 rank induction.
These bounds only normalize the manuscript's numerical constants. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A18InductionBounds

open scoped BigOperators

def a18BudgetScale (D r : Nat) (eps : Real) : Real :=
  (2 : Real) ^ (10 * D * r) * eps

/-- The top A17 contribution is at most `9/512` of the induction budget. -/
theorem a18_top_contribution_le_nine512
    {D r : Nat} {eps : Real} (hD : 1 ≤ D) (hr : 1 ≤ r)
    (heps : 0 ≤ eps) :
    2 * (2 : Real) ^ (10 * (D - 1) * (r - 1)) * eps +
      4 * (2 : Real) ^ (2 * D) * (2 : Real) ^ (10 * D * (r - 1)) * eps ≤
        (9 / 512 : Real) * a18BudgetScale D r eps := by
  let d0 := D - 1
  let r0 := r - 1
  have hd0 : d0 + 1 = D := by dsimp [d0]; omega
  have hr0 : r0 + 1 = r := by dsimp [r0]; omega
  have hd0nonneg : 0 ≤ d0 := Nat.zero_le _
  have hr0nonneg : 0 ≤ r0 := Nat.zero_le _
  have hexp1 : 10 * d0 * r0 + 10 ≤ 10 * D * r := by
    rw [← hd0, ← hr0]
    nlinarith [mul_nonneg hd0nonneg hr0nonneg]
  have hexp2 : 2 * D + 10 * D * r0 + 8 ≤ 10 * D * r := by
    rw [← hd0, ← hr0]
    nlinarith [mul_nonneg hd0nonneg hr0nonneg]
  have hpow1 : (2 : Real) ^ (10 * d0 * r0 + 10) ≤
      (2 : Real) ^ (10 * D * r) :=
    pow_le_pow_right₀ (by norm_num) hexp1
  have hpow2 : (2 : Real) ^ (2 * D + 10 * D * r0 + 8) ≤
      (2 : Real) ^ (10 * D * r) :=
    pow_le_pow_right₀ (by norm_num) hexp2
  have hfirst : 2 * (2 : Real) ^ (10 * d0 * r0) * eps ≤
      a18BudgetScale D r eps / 512 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 512)]
    calc
      (2 * (2 : Real) ^ (10 * d0 * r0) * eps) * 512 =
          (2 : Real) ^ (10 * d0 * r0 + 10) * eps := by
            norm_num [pow_add]
            ring
      _ ≤ (2 : Real) ^ (10 * D * r) * eps :=
        mul_le_mul_of_nonneg_right hpow1 heps
      _ = a18BudgetScale D r eps := by rfl
  have hsecond : 4 * (2 : Real) ^ (2 * D) *
      (2 : Real) ^ (10 * D * r0) * eps ≤
        a18BudgetScale D r eps / 64 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 64)]
    calc
      (4 * (2 : Real) ^ (2 * D) *
          (2 : Real) ^ (10 * D * r0) * eps) * 64 =
          (2 : Real) ^ (2 * D + 10 * D * r0 + 8) * eps := by
            norm_num [pow_add]
            ring
      _ ≤ (2 : Real) ^ (10 * D * r) * eps :=
        mul_le_mul_of_nonneg_right hpow2 heps
      _ = a18BudgetScale D r eps := by rfl
  calc
    _ ≤ a18BudgetScale D r eps / 512 +
          a18BudgetScale D r eps / 64 := add_le_add hfirst hsecond
    _ = (9 / 512 : Real) * a18BudgetScale D r eps := by ring

private theorem a18_geometric_sum_le {D r : Nat} (hr : 1 ≤ r) :
    (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) ≤
      (2 : Real) ^ (5 * D * r) / 31 := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_range_succ]
      have hq : (32 : Real) ≤ (2 : Real) ^ (5 * r) := by
        have he : 5 ≤ 5 * r := by omega
        calc
          (32 : Real) = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (5 * r) := pow_le_pow_right₀ (by norm_num) he
      have hpow : (2 : Real) ^ (5 * (D + 1) * r) =
          (2 : Real) ^ (5 * D * r) * (2 : Real) ^ (5 * r) := by
        rw [← pow_add]
        congr 1
        ring
      have hx : 0 ≤ (2 : Real) ^ (5 * D * r) := by positivity
      calc
        (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) +
            (2 : Real) ^ (5 * D * r) ≤
          (2 : Real) ^ (5 * D * r) / 31 +
            (2 : Real) ^ (5 * D * r) := add_le_add ih le_rfl
        _ ≤ ((2 : Real) ^ (5 * r) / 31) *
            (2 : Real) ^ (5 * D * r) := by
          nlinarith [mul_le_mul_of_nonneg_right hq hx]
        _ = (2 : Real) ^ (5 * (D + 1) * r) / 31 := by rw [hpow]; ring

/-- The square of the sum of all lower-level square-root bounds is at most
`K/961`; this preserves the cross terms in the outer induction. -/
theorem a18_lower_levels_square_le
    {D r : Nat} {eps : Real} (hr : 1 ≤ r) (heps : 0 ≤ eps) :
    ((∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) ^ 2) * eps ≤
      a18BudgetScale D r eps / 961 := by
  have hsum := a18_geometric_sum_le (D := D) hr
  have hsum_nonneg :
      0 ≤ ∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r) := by
    exact Finset.sum_nonneg fun i hi => by positivity
  have hsq :
      (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) ^ 2 ≤
        ((2 : Real) ^ (5 * D * r) / 31) ^ 2 := by
    have hright : 0 ≤ (2 : Real) ^ (5 * D * r) / 31 := by positivity
    have hsumPlus : 0 ≤
        (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) +
          (2 : Real) ^ (5 * D * r) / 31 := by linarith
    have hdiff : 0 ≤ (2 : Real) ^ (5 * D * r) / 31 -
        (∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) :=
      sub_nonneg.mpr hsum
    nlinarith [mul_nonneg hsumPlus hdiff]
  calc
    _ ≤ ((2 : Real) ^ (5 * D * r) / 31) ^ 2 * eps :=
      mul_le_mul_of_nonneg_right hsq heps
    _ = a18BudgetScale D r eps / 961 := by
      simp only [div_pow]
      rw [← pow_mul]
      have hexp : 5 * D * r * 2 = 10 * D * r := by ring
      rw [hexp]
      norm_num [a18BudgetScale] <;> ring

/-- The manuscript's two lower-level contributions fit inside half of the
budget, including the zero-epsilon boundary case. -/
theorem a18_lower_absorption {D r : Nat} {eps : Real}
    (hr : 1 ≤ r) (heps : 0 ≤ eps) :
    a18BudgetScale D r eps / 2 +
      2 * (((∑ i ∈ Finset.range D, (2 : Real) ^ (5 * i * r)) ^ 2) * eps) ≤
        a18BudgetScale D r eps := by
  have hlow := a18_lower_levels_square_le (D := D) hr heps
  have hK : 0 ≤ a18BudgetScale D r eps := by
    unfold a18BudgetScale
    positivity
  calc
    _ ≤ a18BudgetScale D r eps / 2 +
        2 * (a18BudgetScale D r eps / 961) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlow (by norm_num))
    _ ≤ a18BudgetScale D r eps := by
      have hc : (1 / 2 : Real) + 2 / 961 ≤ 1 := by norm_num
      calc
        a18BudgetScale D r eps / 2 +
            2 * (a18BudgetScale D r eps / 961) =
          ((1 / 2 : Real) + 2 / 961) * a18BudgetScale D r eps := by ring
        _ ≤ 1 * a18BudgetScale D r eps :=
          mul_le_mul_of_nonneg_right hc hK
        _ = a18BudgetScale D r eps := by ring

/-- The normalized L2 size of a complex-valued function on a nonempty finite
uniform space. -/
noncomputable def a18UniformL2 {X : Type*} [Fintype X] [Nonempty X] (f : X → Complex) : Real :=
  Real.sqrt ((∑ x : X, Complex.normSq (f x)) / (Fintype.card X : Real))

private theorem a18_uniformL2_add_le {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Complex) :
    a18UniformL2 (fun x => f x + g x) ≤ a18UniformL2 f + a18UniformL2 g := by
  classical
  let N : Real := Fintype.card X
  have hN : 0 < N := by positivity
  have hraw := Real.Lp_add_le_of_nonneg (s := (Finset.univ : Finset X))
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖) (p := (2 : Real)) (by norm_num)
    (by intro x hx; exact norm_nonneg _) (by intro x hx; exact norm_nonneg _)
  have hraw' :
      Real.sqrt (∑ x : X, (‖f x‖ + ‖g x‖) ^ 2) ≤
        Real.sqrt (∑ x : X, ‖f x‖ ^ 2) + Real.sqrt (∑ x : X, ‖g x‖ ^ 2) := by
    simpa only [← Real.rpow_natCast, Real.sqrt_eq_rpow, Nat.cast_ofNat] using hraw
  have hpoint : ∀ x : X, Complex.normSq (f x + g x) ≤
      (‖f x‖ + ‖g x‖) ^ 2 := by
    intro x
    rw [Complex.normSq_eq_norm_sq]
    have hn := norm_add_le (f x) (g x)
    have hn1 : 0 ≤ ‖f x + g x‖ := norm_nonneg _
    have hn0 : 0 ≤ ‖f x‖ + ‖g x‖ := by positivity
    nlinarith [sq_nonneg (‖f x + g x‖), sq_nonneg (‖f x‖ + ‖g x‖)]
  have hsum : (∑ x : X, Complex.normSq (f x + g x)) ≤
      ∑ x : X, (‖f x‖ + ‖g x‖) ^ 2 :=
    Finset.sum_le_sum fun x _ => hpoint x
  have hsumf : 0 ≤ ∑ x : X, Complex.normSq (f x) :=
    Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _
  have hsumg : 0 ≤ ∑ x : X, Complex.normSq (g x) :=
    Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _
  have hsumfg : 0 ≤ ∑ x : X, Complex.normSq (f x + g x) :=
    Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _
  have hnormf : (∑ x : X, ‖f x‖ ^ 2) = ∑ x : X, Complex.normSq (f x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Complex.normSq_eq_norm_sq (z := f x)).symm
  have hnormg : (∑ x : X, ‖g x‖ ^ 2) = ∑ x : X, Complex.normSq (g x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (Complex.normSq_eq_norm_sq (z := g x)).symm
  have hraw'' :
      Real.sqrt (∑ x : X, Complex.normSq (f x + g x)) ≤
        Real.sqrt (∑ x : X, Complex.normSq (f x)) +
          Real.sqrt (∑ x : X, Complex.normSq (g x)) := by
    calc
      _ ≤ Real.sqrt (∑ x : X, (‖f x‖ + ‖g x‖) ^ 2) := Real.sqrt_le_sqrt hsum
      _ ≤ _ := by simpa only [hnormf, hnormg] using hraw'
  have hdiv (s : Real) (hs : 0 ≤ s) :
      Real.sqrt (s / N) = Real.sqrt s / Real.sqrt N := Real.sqrt_div hs N
  unfold a18UniformL2
  rw [hdiv _ hsumfg, hdiv _ hsumf, hdiv _ hsumg]
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hrawdiv := div_le_div_of_nonneg_right hraw'' (by positivity : 0 ≤ Real.sqrt N)
  simpa only [add_div] using hrawdiv

/-- Finite-sum Minkowski for normalized L2 on an arbitrary nonempty finite
uniform carrier. The level index set may be empty, so zero-energy boundaries
need no positivity assumption on any summand. -/
theorem a18_uniformL2_finset_sum_le {X I : Type*} [Fintype X] [Nonempty X]
    (s : Finset I) (g : I → X → Complex) :
    a18UniformL2 (fun x => ∑ i ∈ s, g i x) ≤
      ∑ i ∈ s, a18UniformL2 (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [a18UniformL2]
  | @insert i s hi ih =>
      have hsum : (fun x : X => ∑ j ∈ insert i s, g j x) =
          (fun x => g i x + ∑ j ∈ s, g j x) := by
        funext x
        rw [Finset.sum_insert hi]
      rw [hsum, Finset.sum_insert hi]
      exact (a18_uniformL2_add_le (g i) (fun x => ∑ j ∈ s, g j x)).trans
        (add_le_add le_rfl ih)

end PvNP.RealizableHardness.ActualBinaryMatrixHC46A18InductionBounds
