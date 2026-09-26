import PvNP.RealizableHardness.ActualThreeSatCompileDataFp

/-!
Checks for thin `encodeCompileFn ∈ Complexity.FP`.

`encodeCompileFn` is `Tree.encode` of the `compileData` layout (two
`1/2` weights, one clause-0 3-OR, budget `1`).  Does not inhabit
`hSrcCmmsa`.  Not `No` on unsat.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCompileDataFpChecks

open PvNP.RealizableHardness.ActualThreeSatCompileDataFp
open PvNP.RealizableHardness.ActualThreeSatClauseOrFp
open PvNP.RealizableHardness.CMMSAEncoding
open PvNP.RealizableHardness.CMMSACodec
open Complexity

#check twoHalvesEnc_eq
#check formulasListEnc_mem_FP
#check encodeCompileFn
#check encodeCompileFn_mem_FP
#check encodeCompileFn_eq_dataTree
#check encodeCompileFn_ne_id

example : encodeCompileFn ∈ Complexity.FP := encodeCompileFn_mem_FP

example : encodeCompileFn [] ≠ [] := encodeCompileFn_ne_id

example : twoHalvesEnc =
    Tree.encode (listTree [ratTree ((1 : Rat) / 2), ratTree ((1 : Rat) / 2)]) :=
  twoHalvesEnc_eq

#print axioms encodeCompileFn_mem_FP
#print axioms encodeCompileFn_eq_dataTree
#print axioms encodeCompileFn_ne_id
#print axioms twoHalvesEnc_eq
#print axioms formulasListEnc_mem_FP

end PvNP.RealizableHardness.ActualThreeSatCompileDataFpChecks
