import PvNP.RealizableHardness.ActualThreeSatRofNo

/-!
Checks for the Grassmann-alphabet tape-dependent `No` packing of unsat
well-formed 3SAT encodings.

Does not inhabit `hSrcCmmsa` (not a Yes-map).  Not 8-symbol `graphData`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatRofNoChecks

open PvNP.RealizableHardness.ActualThreeSatRofNo
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.CMMSACodec
open Complexity.SAT

#check rofNoData
#check rofNoData_valid
#check rofNoInstance_no
#check rofNoEnc_mem_no
#check rofNoEnc_no_of_unsat_wellformed
#check rofNoEnc_ne_id

example (L : Nat) (h : 256 ≤ mOf L) (z : List Bool) :
    Valid L (rofNoData L z) :=
  rofNoData_valid h z

#print axioms rofNoData_valid
#print axioms rofNoInstance_no
#print axioms rofNoEnc_no_of_unsat_wellformed
#print axioms rofNoEnc_ne_id

end PvNP.RealizableHardness.ActualThreeSatRofNoChecks
