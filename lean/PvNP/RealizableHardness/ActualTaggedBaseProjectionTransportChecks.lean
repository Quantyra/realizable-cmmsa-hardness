import PvNP.RealizableHardness.ActualTaggedBaseProjectionTransport

namespace PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualQuestionMassBridge
open scoped BigOperators
noncomputable section

#check actualTaggedUniformMean_baseProjection_eq
#check actualTaggedGoodMean_baseProjection_le_four_thirds

#print axioms actualTaggedUniformMean_baseProjection_eq
#print axioms actualTaggedGoodMean_baseProjection_le_four_thirds

def smallActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

def zeroBaseScore : (Fin 0 → smallActual.RowId) → ℝ := fun _ => 0

example :
    actualTaggedUniformMean smallActual 1 0
      (fun u => zeroBaseScore (baseProjection u)) =
      (∑ q : Fin 0 → smallActual.RowId, zeroBaseScore q) /
        (Fintype.card (Fin 0 → smallActual.RowId) : ℝ) := by
  apply actualTaggedUniformMean_baseProjection_eq smallActual
  norm_num

def twoRowActual : ActualOccurrenceAllocation.Instance 1 2 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

def nonconstantBaseScore : (Fin 2 → twoRowActual.RowId) → ℝ :=
  fun q => if q 0 = q 1 then 1 else 0

def equalBase : Fin 2 → twoRowActual.RowId := fun _ => Sum.inl 0

def unequalBase : Fin 2 → twoRowActual.RowId := fun j =>
  if j = 0 then Sum.inl 0 else Sum.inl 1

example : nonconstantBaseScore equalBase = 1 := by
  simp [nonconstantBaseScore, equalBase]

example : nonconstantBaseScore unequalBase = 0 := by
  simp [nonconstantBaseScore, unequalBase]

example :
    actualTaggedGoodMean twoRowActual (actualPaddingCopies 2 4) 2
        (fun u => nonconstantBaseScore (baseProjection u)) ≤
      (4 : ℝ) / 3 *
        ((∑ q : Fin 2 → twoRowActual.RowId, nonconstantBaseScore q) /
          (Fintype.card (Fin 2 → twoRowActual.RowId) : ℝ)) := by
  apply actualTaggedGoodMean_baseProjection_le_four_thirds
  · norm_num
  · norm_num
  · intro q
    dsimp [nonconstantBaseScore]
    split_ifs <;> norm_num

end
end PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
