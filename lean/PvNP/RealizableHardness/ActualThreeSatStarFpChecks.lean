import PvNP.RealizableHardness.ActualThreeSatStarFp

/-!
Checks for Grassmann-alphabet `starEncFn ∈ Complexity.FP`.

`starEncFn L` is `Tree.encode` of the `paramStarData` layout of a 1-clause
3CNF at alphabet `ROf L`.  Does not inhabit `hSrcCmmsa`.  Not `No` on unsat.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarFpChecks

open PvNP.RealizableHardness.ActualThreeSatStarFp
open PvNP.RealizableHardness.ActualThreeSatCompileDataFp
open PvNP.RealizableHardness.ActualThreeSatClauseOrFp
open PvNP.RealizableHardness.CMMSAEncoding
open PvNP.RealizableHardness.CMMSACodec
open PvNP.RealizableHardness.ActualHeadlineParameters
open Complexity

#check grassWeightsEnc_eq
#check starEncFn
#check starEncFn_mem_FP
#check starEncFn_eq_dataTree
#check starEncFn_ne_id

example (L : Nat) : starEncFn L ∈ Complexity.FP := starEncFn_mem_FP L

example (L : Nat) : starEncFn L [] ≠ [] := starEncFn_ne_id L

#print axioms starEncFn_mem_FP
#print axioms starEncFn_eq_dataTree
#print axioms starEncFn_ne_id
#print axioms grassWeightsEnc_eq

end PvNP.RealizableHardness.ActualThreeSatStarFpChecks
