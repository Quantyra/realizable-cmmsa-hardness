import PvNP.RealizableHardness.ActualConditionalTheorem1Core
import PvNP.RealizableHardness.ActualFiniteLaw

/-!
The manuscript's late-τ YES union bound on an actual finite probability law.
The hypotheses about the outer instance and the resampled block marginals are
kept visible. They are not consequences of this probability calculation.
-/

namespace PvNP.RealizableHardness.ActualLateTauYesComposition

open ActualFiniteLaw
open ActualConditionalTheorem1Core

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

def badBlocks (m : Nat) (bad : Fin (m + 1) → Finset Ω) : Finset Ω :=
  Finset.univ.biUnion bad

/-- Counts every original and clique-resampled block, even when their failures
overlap. No independence among the blocks is required. -/
theorem badBlocks_mass_le (m : Nat) (bad : Fin (m + 1) → Finset Ω) :
    eventMass μ (badBlocks m bad) ≤
      ∑ i : Fin (m + 1), eventMass μ (bad i) := by
  classical
  unfold eventMass badBlocks
  have hleft : (∑ ω ∈ Finset.univ.biUnion bad, μ.mass ω) =
      ∑ ω : Ω, if ω ∈ Finset.univ.biUnion bad then μ.mass ω else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext ω
    simp
  have hright : (∑ i : Fin (m + 1), ∑ ω ∈ bad i, μ.mass ω) =
      ∑ ω : Ω, ∑ i : Fin (m + 1), if ω ∈ bad i then μ.mass ω else 0 := by
    rw [Finset.sum_comm]
    simp
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ω ∈ Finset.univ.biUnion bad
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hω
    have hsingle : μ.mass ω ≤
        ∑ j : Fin (m + 1), if ω ∈ bad j then μ.mass ω else 0 := by
      simpa [hi] using (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (m + 1))))
        (f := fun j => if ω ∈ bad j then μ.mass ω else 0)
        (fun j _ => by split_ifs <;> simp [μ.nonneg ω]) (Finset.mem_univ i))
    simpa [hω] using hsingle
  · simpa [hω] using (Finset.sum_nonneg
      (s := (Finset.univ : Finset (Fin (m + 1))))
      (fun i _ => by split_ifs <;> simp [μ.nonneg ω]))

/-- Exact conditional YES composition. `bad i` is the equation failure of
block `i`; `legitimate` is the event on which the PCP sampler is defined.
The numerator premise is deliberately the joint event in the source draw.
Its derivation for every resampled block remains a manuscript obligation. -/
theorem conditioned_yes_failure_le
    (m J : Nat) (τ ε₁ a : ℚ) (hJ : 0 < J) (hτ : 0 < τ)
    (hε : ε₁ ≤ outerYesError m J τ)
    (legitimate : Finset Ω) (bad : Fin (m + 1) → Finset Ω)
    (hlegit : eventMass μ legitimate = 1 - a)
    (ha : a ≤ 1 / 4)
    (hblock : ∀ i, eventMass μ (legitimate ∩ bad i) ≤ (J : ℚ) * ε₁) :
    eventMass μ (legitimate ∩ badBlocks m bad) / eventMass μ legitimate ≤ τ / 75 := by
  have hden : 0 < eventMass μ legitimate := by rw [hlegit]; linarith
  have hset : legitimate ∩ badBlocks m bad =
      badBlocks m (fun i => legitimate ∩ bad i) := by
    ext ω
    simp [badBlocks, Finset.mem_biUnion]
  have hsum : (∑ i : Fin (m + 1), eventMass μ (legitimate ∩ bad i)) ≤
      ((m + 1 : Nat) : ℚ) * ((J : Nat) : ℚ) * ε₁ := by
    calc
      _ ≤ ∑ _i : Fin (m + 1), (J : ℚ) * ε₁ :=
        Finset.sum_le_sum (fun i _ => hblock i)
      _ = _ := by simp [mul_assoc]
  have hnum : eventMass μ (legitimate ∩ badBlocks m bad) ≤
      ((m + 1 : Nat) : ℚ) * ((J : Nat) : ℚ) * ε₁ := by
    rw [hset]
    exact (badBlocks_mass_le μ m (fun i => legitimate ∩ bad i)).trans hsum
  have hquot := div_le_div_of_nonneg_right hnum hden.le
  rw [hlegit] at hquot ⊢
  exact hquot.trans (conditioned_honest_failure_lt hJ hτ ha hε)

theorem conditioned_goodBlocks_probability_gt
    (m J : Nat) (τ ε₁ a : ℚ) (hJ : 0 < J) (hτ : 0 < τ)
    (hε : ε₁ ≤ outerYesError m J τ)
    (legitimate : Finset Ω) (bad : Fin (m + 1) → Finset Ω)
    (hlegit : eventMass μ legitimate = 1 - a)
    (ha : a ≤ 1 / 4)
    (hblock : ∀ i, eventMass μ (legitimate ∩ bad i) ≤ (J : ℚ) * ε₁) :
    1 - τ < 1 - eventMass μ (legitimate ∩ badBlocks m bad) /
      eventMass μ legitimate := by
  have h := conditioned_yes_failure_le μ m J τ ε₁ a hJ hτ hε
    legitimate bad hlegit ha hblock
  linarith

end
end PvNP.RealizableHardness.ActualLateTauYesComposition
