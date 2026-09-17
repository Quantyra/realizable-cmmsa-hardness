import PvNP.RealizableHardness.WeightRounding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite cumulative rounding. Product concentration and encoded runtime are separate obligations. -/
namespace PvNP.RealizableHardness.FiniteSampling
open scoped BigOperators

def cumulative (p : ℕ → ℚ) (j : ℕ) : ℚ := ∑ i ∈ Finset.range j, p i

def cut (p : ℕ → ℚ) (D j : ℕ) : ℕ := ⌊(D : ℚ) * cumulative p j⌋₊

def roundedCumulative (p : ℕ → ℚ) (D j : ℕ) : ℚ := (cut p D j : ℚ) / D

def mass (p : ℕ → ℚ) (D i : ℕ) : ℚ :=
  roundedCumulative p D (i + 1) - roundedCumulative p D i

def eventMass (p : ℕ → ℚ) (S : ℕ) (event : ℕ → Bool) : ℚ :=
  ∑ i ∈ Finset.range S, if event i then p i else 0

@[simp] theorem cumulative_zero (p : ℕ → ℚ) : cumulative p 0 = 0 := by
  simp [cumulative]

@[simp] theorem cumulative_succ (p : ℕ → ℚ) (j : ℕ) :
    cumulative p (j + 1) = cumulative p j + p j := by
  simp [cumulative, Finset.sum_range_succ]

theorem cumulative_nonneg (p : ℕ → ℚ) (hp : ∀ i, 0 ≤ p i) (j : ℕ) :
    0 ≤ cumulative p j := Finset.sum_nonneg (fun i _ => hp i)

theorem cut_mono (p : ℕ → ℚ) (D : ℕ) (hp : ∀ i, 0 ≤ p i) (j : ℕ) :
    cut p D j ≤ cut p D (j + 1) := by
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
  rw [cumulative_succ]
  exact le_add_of_nonneg_right (hp j)

theorem cumulative_error (p : ℕ → ℚ) (D : ℕ) (hD : 0 < D)
    (hp : ∀ i, 0 ≤ p i) (j : ℕ) :
    0 ≤ cumulative p j - roundedCumulative p D j ∧
    cumulative p j - roundedCumulative p D j < 1 / D := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hlo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) (cumulative_nonneg p hp j))
  have hhi := Nat.lt_floor_add_one ((D : ℚ) * cumulative p j)
  change 0 ≤ cumulative p j - (cut p D j : ℚ) / D ∧
    cumulative p j - (cut p D j : ℚ) / D < 1 / D
  change (cut p D j : ℚ) ≤ (D : ℚ) * cumulative p j at hlo
  change (D : ℚ) * cumulative p j < (cut p D j : ℚ) + 1 at hhi
  constructor
  · have := (div_le_iff₀ hDq).mpr (by nlinarith : (cut p D j : ℚ) ≤ cumulative p j * D)
    linarith
  · apply (lt_div_iff₀ hDq).mpr
    have hc : ((cut p D j : ℚ) / D) * D = cut p D j := div_mul_cancel₀ _ hDq.ne'
    nlinarith

theorem mass_nonneg (p : ℕ → ℚ) (D : ℕ) (hp : ∀ i, 0 ≤ p i) (j : ℕ) :
    0 ≤ mass p D j := by
  apply sub_nonneg.mpr
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg D)
  exact_mod_cast cut_mono p D hp j

theorem mass_error (p : ℕ → ℚ) (D : ℕ) (hD : 0 < D)
    (hp : ∀ i, 0 ≤ p i) (j : ℕ) : |mass p D j - p j| ≤ 1 / D := by
  have h0 := cumulative_error p D hD hp j
  have h1 := cumulative_error p D hD hp (j + 1)
  rw [cumulative_succ] at h1
  unfold mass
  apply abs_le.mpr
  constructor <;> linarith

theorem mass_sum (p : ℕ → ℚ) (D S : ℕ) (hD : 0 < D)
    (hnorm : cumulative p S = 1) : ∑ i ∈ Finset.range S, mass p D i = 1 := by
  have htel : ∀ n, (∑ i ∈ Finset.range n, mass p D i) =
      roundedCumulative p D n - roundedCumulative p D 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; unfold mass; ring
  rw [htel]
  simp [roundedCumulative, cut, hnorm, (by exact_mod_cast hD.ne' : (D : ℚ) ≠ 0)]

theorem event_error (p : ℕ → ℚ) (D S : ℕ) (hD : 0 < D)
    (hp : ∀ i, 0 ≤ p i) (event : ℕ → Bool) :
    |eventMass (mass p D) S event - eventMass p S event| ≤ (S : ℚ) / D := by
  unfold eventMass
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range S, |(if event i then mass p D i else 0) -
        (if event i then p i else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range S, (1 : ℚ) / D := by
      apply Finset.sum_le_sum
      intro i _
      cases hi : event i
      · simp [hi]
      · simpa [hi] using mass_error p D hD hp i
    _ = _ := by simp [div_eq_mul_inv]

/-- The manuscript's dyadic precision condition controls every event, hence statistical distance. -/
theorem event_error_of_precision (p : ℕ → ℚ) (S b : ℕ) (eps : ℚ)
    (hp : ∀ i, 0 ≤ p i) (heps : 0 < eps)
    (hgrid : 8 * (S : ℚ) / eps ≤ ((2 ^ b : ℕ) : ℚ)) (event : ℕ → Bool) :
    |eventMass (mass p (2 ^ b)) S event - eventMass p S event| ≤ eps / 8 := by
  have hD : 0 < (2 : ℕ) ^ b := pow_pos (by omega) _
  have hDq : (0 : ℚ) < ((2 ^ b : ℕ) : ℚ) := by exact_mod_cast hD
  have h := (div_le_iff₀ heps).mp hgrid
  apply (event_error p (2 ^ b) S hD hp event).trans
  apply (div_le_iff₀ hDq).mpr
  nlinarith


/-- Finite product law for independent trials; coordinates retain their indices. -/
def trialMass {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ) (draw : Fin M → A) : ℚ :=
  ∏ i, q (draw i)

theorem trialMass_nonneg {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (hq : ∀ a, 0 ≤ q a) (draw : Fin M → A) : 0 ≤ trialMass q M draw :=
  Finset.prod_nonneg (fun i _ => hq (draw i))

theorem trialMass_sum {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (hnorm : ∑ a, q a = 1) : ∑ draw, trialMass q M draw = 1 := by
  unfold trialMass
  rw [← Fintype.prod_sum]
  simp [hnorm]

/-- Full cylinder-event factorization proves independence under the concrete finite product law. -/
theorem trial_event_factorization {A : Type*} [Fintype A] (q : A → ℚ) (M : ℕ)
    (event : Fin M → A → Bool) :
    (∑ draw : Fin M → A, if (∀ i, event i (draw i) = true) then trialMass q M draw else 0) =
      ∏ i, ∑ a, if event i a then q a else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro draw _
  by_cases h : ∀ i, event i (draw i) = true
  · simp [h, trialMass]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- All Boolean assignments, with cardinality exactly 2^N rather than an unspecified class size. -/
theorem assignment_count (N : ℕ) : Fintype.card (Fin N → Bool) = 2 ^ N := by simp

/-- Explicit binary positional indexing of a power-of-two materialized list. -/
def listSampler {A : Type*} (b : ℕ) (entries : Fin (2 ^ b) → A)
    (bits : Fin b → Fin 2) : A := entries (finFunctionFinEquiv bits)

/-- Uniform b-bit input samples the indexed list exactly, retaining duplicate entries. -/
theorem listSampler_exact {A : Type*} (b : ℕ) (entries : Fin (2 ^ b) → A) (event : A → Bool) :
    average (fun bits : Fin b → Fin 2 => event (listSampler b entries bits)) =
      average (fun i : Fin (2 ^ b) => event (entries i)) := by
  unfold average listSampler
  have hsum := (finFunctionFinEquiv : (Fin b → Fin 2) ≃ Fin (2 ^ b)).sum_comp
    (fun i => if event (entries i) then (1 : ℚ) else 0)
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [hsum]

end PvNP.RealizableHardness.FiniteSampling