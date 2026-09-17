import PvNP.RealizableHardness.ActualOccurrenceOrdinals
namespace PvNP.RealizableHardness.ActualOccurrenceOrdinalsChecks
open ActualOccurrenceAllocation ActualOccurrenceOrdinals
#print axioms scanBefore_eq_prefix_count
#print axioms scanBefore_eq_filtered_idxOf
#print axioms scanOrdinal_eq_prefix_count
#print axioms scanOrdinal_eq_ordinal
#print axioms scanOrdinal_lt_size
#print axioms scanBefore_le_length
#print axioms scanOrdinal_le_slots
#print axioms unaryAnswer_length_le
#check scanOrdinal
#check scanOrdinal_eq_ordinal
#check scanOrdinal_lt_size
example : scanBefore (fun n : Nat => decide (n % 2 = 0)) 4 [0,1,2,3,4,6] = 2 := by decide
example : scanBefore (fun _ : Nat => true) 3 [3,4,5] = 0 := by decide
example : scanBefore (fun _ : Nat => true) 3 [] = 0 := by decide
example {N m : Nat} (I : Instance N m) (o : Slot m) :
    scanOrdinal I.vars o = (I.ordinal (I.owner o) (Subtype.mk o rfl)).val := scanOrdinal_eq_ordinal I o
end PvNP.RealizableHardness.ActualOccurrenceOrdinalsChecks
