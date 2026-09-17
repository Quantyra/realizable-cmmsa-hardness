import PvNP.RealizableHardness.ActualSourceFirstOccurrence
namespace PvNP.RealizableHardness.ActualSourceFirstOccurrenceChecks
open Complexity ActualSourceNormalization ActualCompactSourceLookup ActualSourceFirstOccurrence
#print axioms tableClock_mem_FP
#print axioms tableClock_correct
#print axioms hit_mem_FP
#print axioms firstFn_mem_FP
#print axioms rank_decode
#print axioms flatten_get_row
#print axioms ownerLookup_flatten
#print axioms hit_at
#print axioms no_earlier_label
#print axioms hit_first
#print axioms hit_before_first
#print axioms search_correct
#print axioms firstFn_correct
#print axioms output_length_lt
#print axioms input_length_bound
#print axioms search_wire_length
example : Membership.mem FP firstFn := firstFn_mem_FP
example (S : Source) (r : Fin S.1.length) (i : Fin 3) :
    firstFn (lookupInput (table S) (3*r.val+i.val)) =
      List.replicate (first S (tripleLabel S.1[r.val] i)) true := firstFn_correct S r i
example (S : Source) (v : Nat) (hv : v ∈ flatten S) (k : Nat) (hk : k < first S v) :
    hit (pair (pair (table S) (DataEncode.bitstringEncode v))
      (List.replicate k true)) = [] := hit_before_first S v hv k hk
example : first ([(7, (2, 7)), (7, (2, 7))], [false, true]) 7 = 0 := by decide
example : first ([(7, (2, 7)), (7, (2, 7))], [false, true]) 2 = 1 := by decide
#check firstFn
#check firstFn_correct
#check no_earlier_label
end PvNP.RealizableHardness.ActualSourceFirstOccurrenceChecks
