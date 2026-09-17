import PvNP.RealizableHardness.ActualOccurrenceScan
/-! Uncompiled source checks. -/
namespace PvNP.RealizableHardness.ActualOccurrenceScanChecks
open Complexity ActualOccurrenceAllocation ActualOccurrenceLookup ActualOccurrencePrefix ActualOccurrenceScan
#print axioms sameOwnerMark_mem_FP
#print axioms ordinalScan_mem_FP
#print axioms ownerLookup_rank
#print axioms sameOwnerMark_correct
#print axioms sameOwnerMark_length
#print axioms ordinalScan_length_eq_prefix
#print axioms ordinalScan_length_eq_ordinal
#print axioms ordinalScan_correct
#print axioms ordinalScan_length_lt_size
#print axioms ordinalScan_length_le_slots
#print axioms scan_wire_length
#print axioms scan_valid_wire_bound
#print axioms countOver_wire_length
#check ordinalScan_mem_FP
#check ordinalScan_correct
#check ordinalScan_length_lt_size
example : Membership.mem FP ordinalScan := ordinalScan_mem_FP
example {N m : Nat} (I : Instance N m) (o : Slot m) :
    sameOwnerMark (pair (lookupInput (serializedSource I) (rank o))
      (List.replicate (rank o) true)) = [true] := by rw [sameOwnerMark_correct]; simp
example {N m : Nat} (I : Instance N m) (o : Slot m) :
    (ordinalScan (lookupInput (serializedSource I) (rank o))).length ≤ 3*m :=
  ordinalScan_length_le_slots I o
example (table : List Bool) : (lookupInput table 0).length = 2*table.length+2 := by
  simpa using scan_wire_length table 0
example {N m : Nat} (I : Instance N m) (o : Slot m) :
    ordinalScan (lookupInput (serializedSource I) (rank o)) =
      List.replicate (I.ordinal (I.owner o) (Subtype.mk o rfl)).val true := ordinalScan_correct I o
end PvNP.RealizableHardness.ActualOccurrenceScanChecks
