import PvNP.RealizableHardness.ActualOccurrencePrefix
namespace PvNP.RealizableHardness.ActualOccurrencePrefixChecks
open ActualOccurrenceAllocation ActualOccurrenceOrdinals ActualOccurrencePrefix
#print axioms rank_lt
#print axioms rank_decode
#print axioms rank_injective
#print axioms decode_rank
#print axioms decode_injective
#print axioms map_rank_slotList
#print axioms slotList_eq_decode
#print axioms slotList_idxOf
#print axioms slotList_prefix_take
#print axioms prefix_eq_actual
#print axioms prefix_length
#print axioms prefix_nodup
#print axioms prefix_count_eq_scanOrdinal
#print axioms prefix_count_eq_ordinal
#check prefix_eq_actual
#check prefix_count_eq_scanOrdinal
#check prefix_count_eq_ordinal
example : rank ((1 : Fin 2), (2 : Fin 3)) = 5 := by decide
example : («prefix» ((0 : Fin 1), (0 : Fin 3))).length = 0 := by decide
example : («prefix» ((1 : Fin 2), (1 : Fin 3))).map rank = [0,1,2,3] := by decide
example {N m : Nat} (I : Instance N m) (o : Slot m) :
    («prefix» o).countP (fun a => decide (I.vars a.1 a.2 = I.vars o.1 o.2)) =
      (I.ordinal (I.owner o) (Subtype.mk o rfl)).val := prefix_count_eq_ordinal I o
end PvNP.RealizableHardness.ActualOccurrencePrefixChecks
