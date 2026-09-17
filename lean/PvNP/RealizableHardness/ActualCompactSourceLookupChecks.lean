import PvNP.RealizableHardness.ActualCompactSourceLookup
namespace PvNP.RealizableHardness.ActualCompactSourceLookupChecks
open ActualSourceNormalization ActualCompactSourceLookup Complexity
#print axioms tableFromWire_mem_FP
#print axioms tableFromWire_correct
#print axioms rowCount_mem_FP
#print axioms rowCount_correct
#print axioms slotClock_mem_FP
#print axioms slotClock_length
#print axioms ownerLookup_mem_FP
#print axioms ownerLookup_dispatch
#print axioms ownerLookup_correct
#print axioms validInput_length_le
#print axioms equalityMark_mem_FP
#print axioms equalityMark_correct
#print axioms equalityMark_encoded
example (S : Source) : rowCount (wire S) = List.replicate S.1.length true := rowCount_correct S
example (S : Source) : (slotClock (wire S)).length = 3*S.1.length := slotClock_length S
example : equalityMark (DataEncode.bitstringEncode (2 : Nat))
    (DataEncode.bitstringEncode (3 : Nat)) = [] := by rw [equalityMark_encoded]; decide
example (v : Nat) : equalityMark (DataEncode.bitstringEncode v)
    (DataEncode.bitstringEncode v) = [true] := by rw [equalityMark_encoded]; simp
#check ownerLookup
#check ownerLookup_correct
#check equalityMark_encoded
end PvNP.RealizableHardness.ActualCompactSourceLookupChecks
