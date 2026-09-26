import PvNP.RealizableHardness.ActualThreeSatFpDispatch

/-!
Checks for the FP empty/nonempty CMMSA dispatch.

Does not inhabit `hSrcCmmsa`.  Nonempty sat 3SAT is mapped to `No`, so
this is not `MapReducesVia`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatFpDispatchChecks

open PvNP.RealizableHardness.ActualThreeSatFpDispatch
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualThreeSatGraphYes
open PvNP.RealizableHardness.ActualThreeSatPresentedLeaf
open Complexity.SAT

#check fpDispatch
#check fpDispatch_mem_FP
#check fpDispatch_yes_of_empty
#check fpDispatch_no_of_cons
#check fpDispatch_no_of_unsatCnf
#check fpDispatch_not_mapReduces
#check fpDispatch_ne_id
#check empty_mem_threeSat
#check satUnit_mem_threeSat

example {L : Nat} (h : 256 ≤ mOf L) : fpDispatch L h [] ≠ [] :=
  fpDispatch_ne_id h

example : satUnit.encode ≠ [] := satUnit_encode_ne_nil

#print axioms fpDispatch_mem_FP
#print axioms fpDispatch_yes_of_empty
#print axioms fpDispatch_no_of_cons
#print axioms fpDispatch_no_of_unsatCnf
#print axioms fpDispatch_not_mapReduces
#print axioms fpDispatch_ne_id

end PvNP.RealizableHardness.ActualThreeSatFpDispatchChecks
