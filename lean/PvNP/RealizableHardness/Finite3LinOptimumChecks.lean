import PvNP.RealizableHardness.Finite3LinOptimum

namespace PvNP.RealizableHardness.Finite3LinOptimumChecks
open PvNP.RealizableHardness
open Finite3LinSource
open scoped BigOperators
noncomputable section

#check Finite3LinSource.minViolations
#check Finite3LinSource.minViolations_le_violations
#check Finite3LinSource.exists_violations_eq_minViolations
#check Finite3LinSource.taggedCopy_minViolations
#check Finite3LinSource.minimumViolationRate
#check Finite3LinSource.value
#check Finite3LinSource.taggedCopy_minimumViolationRate
#check Finite3LinSource.taggedCopy_value

#print axioms Finite3LinSource.minViolations
#print axioms Finite3LinSource.minViolations_le_violations
#print axioms Finite3LinSource.exists_violations_eq_minViolations
#print axioms Finite3LinSource.taggedCopy_minViolations
#print axioms Finite3LinSource.minimumViolationRate
#print axioms Finite3LinSource.value
#print axioms Finite3LinSource.taggedCopy_minimumViolationRate
#print axioms Finite3LinSource.taggedCopy_value

def contradictoryTwoRow : Finite3LinSource (Fin 2) (Fin 3) where
  row := fun _ i => i
  rhs := fun q => if q = 0 then 0 else 1
  row_injective := by
    intro q i j h
    exact h

def allZero : Fin 3 → ZMod 2 := fun _ => 0

private theorem contradictoryTwoRow_minViolations : contradictoryTwoRow.minViolations = 1 := by
  apply le_antisymm
  · have h := Finite3LinSource.minViolations_le_violations contradictoryTwoRow allZero
    norm_num [Finite3LinSource.violations, Finite3LinSource.badRow,
      contradictoryTwoRow, allZero] at h ⊢
    exact h
  · rcases Finite3LinSource.exists_violations_eq_minViolations contradictoryTwoRow with ⟨x, hx⟩
    have hpos : 0 < contradictoryTwoRow.violations x := by
      by_cases hs : x 0 + x 1 + x 2 = 0
      · norm_num [Finite3LinSource.violations, Finite3LinSource.badRow,
          contradictoryTwoRow, hs]
      · simp [Finite3LinSource.violations, Finite3LinSource.badRow,
          contradictoryTwoRow, hs]
    rw [hx] at hpos
    omega

example : (contradictoryTwoRow.taggedCopy 0).minViolations = 0 := by
  decide

example : (contradictoryTwoRow.taggedCopy 3).minViolations = 3 := by
  rw [Finite3LinSource.taggedCopy_minViolations, contradictoryTwoRow_minViolations]

example : contradictoryTwoRow.minimumViolationRate = (1 / 2 : Real) := by
  rw [Finite3LinSource.minimumViolationRate, contradictoryTwoRow_minViolations]
  norm_num [Fintype.card_fin]

example : (contradictoryTwoRow.taggedCopy 3).minimumViolationRate = (1 / 2 : Real) := by
  rw [Finite3LinSource.taggedCopy_minimumViolationRate contradictoryTwoRow 3 (by decide) (by decide)]
  rw [Finite3LinSource.minimumViolationRate, contradictoryTwoRow_minViolations]
  norm_num [Fintype.card_fin]

example : contradictoryTwoRow.value = (1 / 2 : Real) := by
  rw [Finite3LinSource.value, Finite3LinSource.minimumViolationRate,
    contradictoryTwoRow_minViolations]
  norm_num [Fintype.card_fin]

example : (contradictoryTwoRow.taggedCopy 3).value = (1 / 2 : Real) := by
  rw [Finite3LinSource.taggedCopy_value contradictoryTwoRow 3 (by decide) (by decide)]
  rw [Finite3LinSource.value, Finite3LinSource.minimumViolationRate,
    contradictoryTwoRow_minViolations]
  norm_num [Fintype.card_fin]

end
end PvNP.RealizableHardness.Finite3LinOptimumChecks
