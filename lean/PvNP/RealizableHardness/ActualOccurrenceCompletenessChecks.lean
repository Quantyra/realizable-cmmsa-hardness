import PvNP.RealizableHardness.ActualOccurrenceCompleteness

namespace PvNP.RealizableHardness.ActualOccurrenceCompletenessChecks
open ActualOccurrenceAllocation ActualOccurrenceAllocation.Instance

#print axioms sourceExtension_port
#print axioms sourceExtension_anchor
#print axioms sourceExtension_original_value
#print axioms sourceExtension_original_bad
#print axioms sourceExtension_original_violations
#print axioms sourceExtension_restrict
#print axioms sourceExtension_cloud_zero
#print axioms sourceExtension_tagged_cloud_zero
#print axioms sourceExtension_violations
#print axioms sourceExtension_filter_length
#print axioms sourceExtension_satisfied
#print axioms sourceExtension_count_bound
#print axioms sourceViolations_zero
#print axioms sourceExtension_empty

#check sourceExtension
#check sourceExtension_violations
#check sourceExtension_filter_length

example {N m : Nat} (I : Instance N m) (y : Fin N → ZMod 2) (o : Slot m) :
    I.sourceExtension y (I.anchor o) = y (I.owner o) := I.sourceExtension_anchor y o
example {N m : Nat} (I : Instance N m) (y : Fin N → ZMod 2) (v : Fin N) :
    ActualEqualityCloud.rowsViolations (I.restrictCloud (I.sourceExtension y) v) = 0 :=
  I.sourceExtension_cloud_zero y v
/-- Unused variables require no separate exceptional assignment or branch. -/
example {N m : Nat} (I : Instance N m) (y : Fin N → ZMod 2) (v : Fin N) (_ : I.size v = 0) :
    ActualEqualityCloud.rowsViolations (I.restrictCloud (I.sourceExtension y) v) = 0 :=
  I.sourceExtension_cloud_zero y v
example {N m : Nat} (I : Instance N m) (y : Fin N → ZMod 2) :
    I.violations (I.sourceExtension y) = I.sourceViolations y := I.sourceExtension_violations y
example {N m : Nat} (I : Instance N m) (y : Fin N → ZMod 2) (h : I.sourceViolations y = 0) :
    I.violations (I.sourceExtension y) = 0 := I.sourceExtension_satisfied y h
example {N : Nat} (I : Instance N 0) (y : Fin N → ZMod 2) :
    I.violations (I.sourceExtension y) = 0 := I.sourceExtension_empty y

end PvNP.RealizableHardness.ActualOccurrenceCompletenessChecks
