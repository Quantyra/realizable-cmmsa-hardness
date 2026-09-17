import PvNP.RealizableHardness.ActualOccurrenceLookup

/-! Source-only checks. No compilation or independent acceptance yet. -/
namespace PvNP.RealizableHardness.ActualOccurrenceLookupChecks
open Complexity ActualOccurrenceAllocation ActualOccurrenceLookup

#print axioms ownerLookup_mem_FP
#print axioms sourceTriples_length
#print axioms sourceTriples_get
#print axioms recFst_source
#print axioms recSnd_source
#print axioms recThd_source
#print axioms ownerLookup_dispatch
#print axioms ownerLookup_correct
#print axioms ownerLookup_length
#print axioms ownerLookup_length_lt
#print axioms lookupInput_length
#print axioms slotCounter_lt
#print axioms validInput_length_le
#print axioms sourceTriples_empty

#check ownerLookup_mem_FP
#check ownerLookup_correct
#check lookupInput_length

example : Membership.mem FP ownerLookup := ownerLookup_mem_FP
example {N m : Nat} (I : Instance N m) (r : Fin m) :
    ownerLookup (lookupInput (serializedSource I) (3*r.val+0)) =
      List.replicate (I.vars r 0).val true := by
  simpa [Instance.owner] using ownerLookup_correct I (r,0)
example {N m : Nat} (I : Instance N m) (r : Fin m) :
    ownerLookup (lookupInput (serializedSource I) (3*r.val+1)) =
      List.replicate (I.vars r 1).val true := by
  simpa [Instance.owner] using ownerLookup_correct I (r,1)
example {N m : Nat} (I : Instance N m) (r : Fin m) :
    ownerLookup (lookupInput (serializedSource I) (3*r.val+2)) =
      List.replicate (I.vars r 2).val true := by
  simpa [Instance.owner] using ownerLookup_correct I (r,2)
example {N m : Nat} (I : Instance N m) (o : Slot m) :
    (lookupInput (serializedSource I) (3*o.1.val+o.2.val)).length <=
      2*(serializedSource I).length+2+3*m := validInput_length_le I o
example {N : Nat} (I : Instance N 0) : sourceTriples I = [] := sourceTriples_empty I

end PvNP.RealizableHardness.ActualOccurrenceLookupChecks
