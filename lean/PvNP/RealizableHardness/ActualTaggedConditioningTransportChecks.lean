import PvNP.RealizableHardness.ActualTaggedConditioningTransport

namespace PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualQuestionMassBridge
open scoped BigOperators
noncomputable section

local instance checksActualRowIdDecidableEq {N m : Nat}
    (I : ActualOccurrenceAllocation.Instance N m) : DecidableEq I.RowId :=
  Classical.decEq _

#check actualTaggedUniformMean
#check actualTaggedGoodMean
#check actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass
#check actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
#check actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg

#print axioms actualTaggedUniformMean
#print axioms actualTaggedGoodMean
#print axioms actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass
#print axioms actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
#print axioms actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg

def smallActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

example : actualTaggedGoodMean smallActual (actualPaddingCopies 0 4) 0
    (fun _ => (0 : ℝ)) =
    actualTaggedUniformMean smallActual (actualPaddingCopies 0 4) 0
      (fun u => if u ∈ actualTaggedGoodQuestions smallActual
        (actualPaddingCopies 0 4) 0 then 0 else 0) /
      (actualTaggedGoodMass smallActual (actualPaddingCopies 0 4) 0 : ℝ) := by
  apply actualTaggedGoodMean_eq_gatedUniformMean_div_goodMass
  norm_num
  norm_num

example : actualTaggedGoodMean smallActual (actualPaddingCopies 0 4) 0
    (fun _ => (1 : ℝ)) ≤
    (4 : ℝ) / 3 * actualTaggedUniformMean smallActual
      (actualPaddingCopies 0 4) 0 (fun _ => (1 : ℝ)) := by
  apply actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
  · norm_num
  · norm_num
  · intro u
    norm_num

example : actualTaggedGoodMean smallActual (actualPaddingCopies 0 4) 0
    (fun _ => (1 : ℝ)) ≤
    2 * actualTaggedUniformMean smallActual
      (actualPaddingCopies 0 4) 0 (fun _ => (1 : ℝ)) := by
  apply actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg
  · norm_num
  · norm_num
  · intro u
    norm_num

def nontrivialScore :
    (Fin 2 → Fin (actualPaddingCopies 2 4) × smallActual.RowId) → ℝ :=
  fun u => if u 0 = u 1 then 1 else 0

example : actualTaggedGoodMean smallActual (actualPaddingCopies 2 4) 2
    nontrivialScore ≤
    (4 : ℝ) / 3 * actualTaggedUniformMean smallActual
      (actualPaddingCopies 2 4) 2 nontrivialScore := by
  apply actualTaggedGoodMean_le_four_thirds_mul_uniformMean_of_nonneg
  · norm_num
  · norm_num
  · intro u
    dsimp [nontrivialScore]
    split_ifs <;> norm_num

example : actualTaggedGoodMean smallActual (actualPaddingCopies 2 4) 2
    nontrivialScore ≤
    2 * actualTaggedUniformMean smallActual
      (actualPaddingCopies 2 4) 2 nontrivialScore := by
  apply actualTaggedGoodMean_le_two_mul_uniformMean_of_nonneg
  · norm_num
  · norm_num
  · intro u
    dsimp [nontrivialScore]
    split_ifs <;> norm_num

end
end PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
