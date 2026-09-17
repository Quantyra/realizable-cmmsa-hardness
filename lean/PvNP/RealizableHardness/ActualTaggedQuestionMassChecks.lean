import PvNP.RealizableHardness.ActualTaggedQuestionMass

namespace PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
open PvNP.RealizableHardness
open PvNP.RealizableHardness.ActualOccurrenceAllocation
open PvNP.RealizableHardness.ActualQuestionMassBridge
noncomputable section

#check actual_conflict_degree_le
#check actual_tagged_row_card
#check actual_tagged_bad_ordered_question_count_le
#check actualPaddingCopies
#check actualPaddingCopies_pos

#print axioms actual_conflict_degree_le
#print axioms actual_tagged_row_card
#print axioms actual_tagged_bad_ordered_question_count_le
#print axioms actualPaddingCopies
#print axioms actualPaddingCopies_pos

def smallActual : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 0

local instance smallActualRowIdDecidableEq : DecidableEq smallActual.RowId :=
  Classical.decEq _

example : True := by
  have h0 := actual_tagged_bad_ordered_question_count_le smallActual 2 0
  have h1 := actual_tagged_bad_ordered_question_count_le smallActual 2 1
  have h2 := actual_tagged_bad_ordered_question_count_le smallActual 2 2
  exact True.intro

example : Fintype.card (Fin 2 × smallActual.RowId) =
    2 * smallActual.rows.length :=
  actual_tagged_row_card smallActual 2

example (J : Nat) : 0 < actualPaddingCopies J 4 :=
  actualPaddingCopies_pos J 4

end
end PvNP.RealizableHardness.ActualQuestionMassBridgeChecks
