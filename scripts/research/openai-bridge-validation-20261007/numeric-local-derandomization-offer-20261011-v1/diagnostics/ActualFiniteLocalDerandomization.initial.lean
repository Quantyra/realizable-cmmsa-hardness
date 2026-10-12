import PvNP.RealizableHardness.ActualFiniteLaw
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Finite private randomness can be removed without giving either player
the other's question. The actual verifier aggregation remains a separate
application. Uncompiled and unaccepted. -/
namespace PvNP.RealizableHardness.ActualFiniteLocalDerandomization

open scoped BigOperators
open ActualFiniteLaw

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance 2000] Classical.decEq

theorem exists_answer_ge_law_mean {A : Type*} [Fintype A] [Nonempty A]
    (μ : FiniteLaw A) (f : A → Real) :
    ∃ a : A, (∑ x : A, (μ.mass x : Real) * f x) ≤ f a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) f Finset.univ_nonempty
  refine ⟨a, ?_⟩
  have hnorm : (∑ x : A, (μ.mass x : Real)) = 1 := by exact_mod_cast μ.normalized
  calc
    _ ≤ ∑ x : A, (μ.mass x : Real) * f a := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left (ha x (Finset.mem_univ x))
      exact_mod_cast μ.nonneg x
    _ = f a := by rw [← Finset.sum_mul, hnorm, one_mul]

variable {Q1 Q2 A B : Type*} [Fintype Q1] [Fintype Q2] [Fintype A] [Fintype B]

/-- The payoff kernel includes all verifier probabilities. -/
def randomizedValue (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B)
    (K : Q1 → Q2 → A → B → Real) : Real :=
  ∑ q : Q1, ∑ a : A, (μ q |>.mass a : Real) *
    ∑ r : Q2, ∑ b : B, (ν r |>.mass b : Real) * K q r a b

def firstFixedValue (f : Q1 → A) (ν : Q2 → FiniteLaw B)
    (K : Q1 → Q2 → A → B → Real) : Real :=
  ∑ q : Q1, ∑ r : Q2, ∑ b : B, (ν r |>.mass b : Real) * K q r (f q) b

def deterministicValue (f : Q1 → A) (g : Q2 → B)
    (K : Q1 → Q2 → A → B → Real) : Real :=
  ∑ q : Q1, ∑ r : Q2, K q r (f q) (g r)

theorem exists_first_fixed_ge_randomized [Nonempty A]
    (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B)
    (K : Q1 → Q2 → A → B → Real) :
    ∃ f : Q1 → A, randomizedValue μ ν K ≤ firstFixedValue f ν K := by
  have hq : ∀ q : Q1, ∃ a : A,
      (∑ x : A, (μ q |>.mass x : Real) *
        ∑ r : Q2, ∑ b : B, (ν r |>.mass b : Real) * K q r x b) ≤
          ∑ r : Q2, ∑ b : B, (ν r |>.mass b : Real) * K q r a b := by
    intro q
    exact exists_answer_ge_law_mean (μ q)
      (fun a => ∑ r : Q2, ∑ b : B, (ν r |>.mass b : Real) * K q r a b)
  choose f hf using hq
  refine ⟨f, ?_⟩
  exact Finset.sum_le_sum (fun q _ => hf q)

/-- Two separate local choices dominate independent private randomness.
Neither deterministic function has the other question as an argument. -/
theorem exists_deterministic_ge_randomized [Nonempty A] [Nonempty B]
    (μ : Q1 → FiniteLaw A) (ν : Q2 → FiniteLaw B)
    (K : Q1 → Q2 → A → B → Real) :
    ∃ f : Q1 → A, ∃ g : Q2 → B,
      randomizedValue μ ν K ≤ deterministicValue f g K := by
  obtain ⟨f, hf⟩ := exists_first_fixed_ge_randomized μ ν K
  have hr : ∀ r : Q2, ∃ b : B,
      (∑ y : B, (ν r |>.mass y : Real) * ∑ q : Q1, K q r (f q) y) ≤
        ∑ q : Q1, K q r (f q) b := by
    intro r
    exact exists_answer_ge_law_mean (ν r) (fun b => ∑ q : Q1, K q r (f q) b)
  choose g hg using hr
  refine ⟨f, g, hf.trans ?_⟩
  calc
    firstFixedValue f ν K =
        ∑ r : Q2, ∑ b : B, (ν r |>.mass b : Real) * ∑ q : Q1, K q r (f q) b := by
      unfold firstFixedValue
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ r : Q2, ∑ q : Q1, K q r (f q) (g r) :=
      Finset.sum_le_sum (fun r _ => hg r)
    _ = deterministicValue f g K := by
      unfold deterministicValue
      exact Finset.sum_comm

end
end PvNP.RealizableHardness.ActualFiniteLocalDerandomization
