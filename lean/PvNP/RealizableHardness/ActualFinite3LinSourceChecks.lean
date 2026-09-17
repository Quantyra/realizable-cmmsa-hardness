import PvNP.RealizableHardness.ActualFinite3LinSource

namespace PvNP.RealizableHardness.ActualFinite3LinSourceChecks
open PvNP.RealizableHardness
open ActualOccurrenceAllocation
open ActualOccurrenceAllocation.Instance
noncomputable section

#check row_injective_of_support_card
#check ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length
#check Finite3LinSource.ofActual
#check Finite3LinSource.ofActual_row
#check Finite3LinSource.ofActual_support
#check Finite3LinSource.ofActual_rhs
#check Finite3LinSource.ofActual_badRow
#check Finite3LinSource.ofActual_violations

#print axioms row_injective_of_support_card
#print axioms ActualOccurrenceAllocation.Instance.rowId_card_eq_rows_length
#print axioms Finite3LinSource.ofActual
#print axioms Finite3LinSource.ofActual_row
#print axioms Finite3LinSource.ofActual_support
#print axioms Finite3LinSource.ofActual_rhs
#print axioms Finite3LinSource.ofActual_badRow
#print axioms Finite3LinSource.ofActual_violations

def violatedSource : ActualOccurrenceAllocation.Instance 1 1 where
  vars := fun _ _ => 0
  rhs := fun _ => 1

local instance violatedRowIdDecidableEq : DecidableEq violatedSource.RowId :=
  Classical.decEq _

def zeroAssignment : violatedSource.GlobalVar → ZMod 2 := fun _ => 0

def originalId : violatedSource.RowId := Sum.inl 0

example : Fintype.card violatedSource.RowId = violatedSource.rows.length :=
  violatedSource.rowId_card_eq_rows_length

example :
    (Finite3LinSource.ofActual violatedSource).support originalId =
      violatedSource.support originalId :=
  Finite3LinSource.ofActual_support violatedSource originalId

example : (Finite3LinSource.ofActual violatedSource).rhs originalId = 1 := by
  rfl

example : violatedSource.badRow zeroAssignment
    (violatedSource.row originalId, violatedSource.rowRhs originalId) = true := by
  norm_num [ActualOccurrenceAllocation.Instance.badRow,
    ActualOccurrenceAllocation.Instance.rowRhs, violatedSource,
    zeroAssignment, originalId]

example : (Finite3LinSource.ofActual violatedSource).badRow zeroAssignment originalId =
    violatedSource.badRow zeroAssignment
      (violatedSource.row originalId, violatedSource.rowRhs originalId) :=
  Finite3LinSource.ofActual_badRow violatedSource zeroAssignment originalId

example : (Finite3LinSource.ofActual violatedSource).violations zeroAssignment =
    violatedSource.violations zeroAssignment :=
  Finite3LinSource.ofActual_violations violatedSource zeroAssignment

end
end PvNP.RealizableHardness.ActualFinite3LinSourceChecks
