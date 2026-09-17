import PvNP.RealizableHardness.ActualSourceNormalizedTable
namespace PvNP.RealizableHardness.ActualSourceNormalizedTableChecks
open Complexity ActualSourceNormalization ActualCompactSourceLookup ActualSourceNormalizedTable
#print axioms unaryRows_length
#print axioms slotArg_mem_FP
#print axioms slotArg_correct
#print axioms renamedField_mem_FP
#print axioms renamedField_correct
#print axioms rowRule_mem_FP
#print axioms rowRule_correct
#print axioms tableFn_mem_FP
#print axioms tableFn_correct
#print axioms dataPair_mem_FP
#print axioms sourceFn_mem_FP
#print axioms sourceFn_correct
#print axioms sourceFn_rhs
#print axioms sourceFn_table
#print axioms sourceFn_length
#print axioms sourceFn_output_polynomial
#print axioms unaryTriple_length
#print axioms tableFn_length_bound
#print axioms sourceFn_length_bound
#print axioms unarySource_empty
#print axioms unarySource_rhs

example (S : Source) : tableFn (table S) = DataEncode.bitstringEncode (unaryRows S) :=
  tableFn_correct S
example (S : Source) : sourceFn (wire S) = DataEncode.bitstringEncode (unarySource S) :=
  sourceFn_correct S
example (S : Source) : sndEnc (sourceFn (wire S)) = DataEncode.bitstringEncode S.2 :=
  sourceFn_rhs S
example : Membership.mem FP sourceFn := sourceFn_mem_FP
example : unarySource ([], []) = ([], []) := unarySource_empty
example : sourceFn (wire ([], [])) = DataEncode.bitstringEncode (unarySource ([], [])) :=
  sourceFn_correct ([], [])
example (S : Source) (v w : Nat) :
    unaryTriple (renameTriple S (v,v,w)) =
      (List.replicate (first S v) true, List.replicate (first S v) true,
       List.replicate (first S w) true) := rfl
example (S : Source) : (unaryRows S).length = S.1.length := unaryRows_length S
#check rowRule_correct
#check tableFn_correct
#check sourceFn_correct
#check sourceFn_output_polynomial
end PvNP.RealizableHardness.ActualSourceNormalizedTableChecks
