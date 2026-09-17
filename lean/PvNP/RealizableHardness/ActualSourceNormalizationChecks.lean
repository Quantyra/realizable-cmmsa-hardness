import PvNP.RealizableHardness.ActualSourceNormalization
namespace PvNP.RealizableHardness.ActualSourceNormalizationChecks
open ActualSourceNormalization
#print axioms flatten_length
#print axioms first_lt
#print axioms get_first
#print axioms first_eq_iff_on_used
#print axioms normalized_label_bound
#print axioms normalized_valid
#print axioms rowValue_lift
#print axioms rowValue_decode
#print axioms violationFlags_lift
#print axioms violationFlags_decode
#print axioms violations_lift
#print axioms violations_decode
example : normalize ([], []) = ([], []) := normalize_empty
example (S : Source) (v w : Nat) :
    renameTriple S (v,v,w) = (first S v,first S v,first S w) :=
  repeated_labels_preserved S v w
example (S : Source) (a : Nat -> ZMod 2) :
    violations (normalize S) (liftAssignment S a) = violations S a := violations_lift S a
example (S : Source) (b : Nat -> ZMod 2) :
    violations S (decodeAssignment S b) = violations (normalize S) b := violations_decode S b
#check wire
#check normalize
#check normalized_label_bound
end PvNP.RealizableHardness.ActualSourceNormalizationChecks
