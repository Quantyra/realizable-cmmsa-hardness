import PvNP.RealizableHardness.ActualFiniteLaw
import Mathlib.Tactic

/-! Finite event monotonicity and a genuine union bound for the accepted
finite probability-law carrier. These lemmas are the probability interface
for finite candidate catalogs; they make no independence assumption. -/

namespace PvNP.RealizableHardness.ActualStarFiniteUnionBound

open PvNP.RealizableHardness.ActualFiniteLaw

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Event mass is monotone under inclusion, using nonnegativity of the law. -/
theorem eventMass_mono {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) {E F : Finset Ω} (hEF : E ⊆ F) :
    eventMass μ E ≤ eventMass μ F := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hEF
    (fun x hx _ => mass_nonneg μ x)

/-- The mass of a finite union of candidate events is at most the sum of
their masses. Repetitions and overlaps among candidates are allowed. -/
theorem eventMass_biUnion_le_sum {Ω Ι : Type*} [Fintype Ω] [Fintype Ι]
    (μ : FiniteLaw Ω) (E : Ι → Finset Ω) :
    eventMass μ (Finset.univ.biUnion E) ≤ ∑ i, eventMass μ (E i) := by
  classical
  let U : Finset Ω := Finset.univ.biUnion E
  have hpoint (x : Ω) :
      (if x ∈ U then μ.mass x else 0) ≤
        ∑ i ∈ (Finset.univ : Finset Ι),
          if x ∈ E i then μ.mass x else 0 := by
    by_cases hu : x ∈ U
    · obtain ⟨i, hiU, hi⟩ := Finset.mem_biUnion.mp hu
      rw [if_pos hu]
      have hterm : (if x ∈ E i then μ.mass x else 0) = μ.mass x := if_pos hi
      have hnonneg : ∀ j ∈ (Finset.univ : Finset Ι),
          0 ≤ (if x ∈ E j then μ.mass x else 0) := by
        intro j hj
        by_cases hxj : x ∈ E j
        · simpa [hxj] using mass_nonneg μ x
        · simp [hxj]
      calc
        μ.mass x = (if x ∈ E i then μ.mass x else 0) := hterm.symm
        _ ≤ ∑ j ∈ (Finset.univ : Finset Ι),
            if x ∈ E j then μ.mass x else 0 := by
          exact Finset.single_le_sum
            (s := (Finset.univ : Finset Ι))
            (f := fun j => if x ∈ E j then μ.mass x else 0)
            hnonneg
            (Finset.mem_univ i)
    · rw [if_neg hu]
      exact Finset.sum_nonneg fun i hi => by
        by_cases hxi : x ∈ E i
        · simpa [hxi] using mass_nonneg μ x
        · simp [hxi]
  calc
    eventMass μ U =
        ∑ x ∈ U, if x ∈ U then μ.mass x else 0 := by
          simp [eventMass]
    _ ≤ ∑ x ∈ (Finset.univ : Finset Ω),
          ∑ i, if x ∈ E i then μ.mass x else 0 := by
            calc
              _ ≤ ∑ x ∈ (Finset.univ : Finset Ω),
                    if x ∈ U then μ.mass x else 0 := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
                      intro x hxU hnot
                      simp [hnot]
              _ ≤ _ := by
                      apply Finset.sum_le_sum
                      intro x hx
                      exact hpoint x
    _ = ∑ i, ∑ x ∈ E i, μ.mass x := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          simp
    _ = ∑ i, eventMass μ (E i) := by
          rfl

end
end PvNP.RealizableHardness.ActualStarFiniteUnionBound
