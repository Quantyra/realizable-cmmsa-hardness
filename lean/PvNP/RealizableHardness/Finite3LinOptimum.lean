import PvNP.RealizableHardness.TaggedFinite3LinSource

namespace PvNP.RealizableHardness
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace Finite3LinSource
variable {Row Var : Type*} [Fintype Row] [Fintype Var]
  [DecidableEq Row] [DecidableEq Var]

private theorem violations_image_nonempty (I : Finite3LinSource Row Var) :
    (Finset.univ.image I.violations).Nonempty := by
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

def minViolations (I : Finite3LinSource Row Var) : Nat :=
  (Finset.univ.image I.violations).min' (violations_image_nonempty I)

theorem minViolations_le_violations (I : Finite3LinSource Row Var)
    (x : Var → ZMod 2) : I.minViolations ≤ I.violations x := by
  unfold minViolations
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem exists_violations_eq_minViolations (I : Finite3LinSource Row Var) :
    ∃ x : Var → ZMod 2, I.violations x = I.minViolations := by
  have hm : I.minViolations ∈ Finset.univ.image I.violations := by
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hm with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

theorem taggedCopy_minViolations (I : Finite3LinSource Row Var) (K : Nat) :
    (I.taggedCopy K).minViolations = K * I.minViolations := by
  apply le_antisymm
  · rcases exists_violations_eq_minViolations I with ⟨x, hx⟩
    have hle := minViolations_le_violations (I.taggedCopy K)
      (repeatAssignment (K := K) x)
    rw [taggedCopy_repeatAssignment_violations, hx] at hle
    exact hle
  · rcases exists_violations_eq_minViolations (I.taggedCopy K) with ⟨y, hy⟩
    rw [← hy, taggedCopy_violations]
    calc
      K * I.minViolations = ∑ _ : Fin K, I.minViolations := by simp
      _ ≤ ∑ k : Fin K, I.violations (restrictAssignment y k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact minViolations_le_violations I (restrictAssignment y k)

def minimumViolationRate (I : Finite3LinSource Row Var) : Real :=
  (I.minViolations : Real) / (Fintype.card Row : Real)

def value (I : Finite3LinSource Row Var) : Real :=
  1 - I.minimumViolationRate

theorem taggedCopy_minimumViolationRate (I : Finite3LinSource Row Var) (K : Nat)
    (hK : 0 < K) (hRow : 0 < Fintype.card Row) :
    (I.taggedCopy K).minimumViolationRate = I.minimumViolationRate := by
  unfold minimumViolationRate
  rw [taggedCopy_minViolations, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.cast_mul, Nat.cast_mul]
  field_simp

theorem taggedCopy_value (I : Finite3LinSource Row Var) (K : Nat)
    (hK : 0 < K) (hRow : 0 < Fintype.card Row) :
    (I.taggedCopy K).value = I.value := by
  unfold value
  rw [taggedCopy_minimumViolationRate I K hK hRow]

end Finite3LinSource

end
end PvNP.RealizableHardness
