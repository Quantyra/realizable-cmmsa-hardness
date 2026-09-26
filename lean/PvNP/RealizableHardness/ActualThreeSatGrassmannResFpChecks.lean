import PvNP.RealizableHardness.ActualThreeSatGrassmannResFp

/-!
Checks for the uniform Grassmann-restriction FP encoder.
Does not inhabit `hSrcCmmsa`.  Always-Yes, not a No-map.
-/
namespace PvNP.RealizableHardness.ActualThreeSatGrassmannResFpChecks

open PvNP.RealizableHardness.ActualThreeSatGrassmannResFp
open PvNP.RealizableHardness.ActualThreeSatGrassmannRes
open PvNP.RealizableHardness.ActualHeadlineParameters
open Complexity

#check resEncFn
#check resEncFn_mem_FP
#check resEncFn_ne_id
#check resFormsEnc_mem_FP
#check resFormsEnc

#print axioms resEncFn_mem_FP
#print axioms resEncFn_ne_id

end PvNP.RealizableHardness.ActualThreeSatGrassmannResFpChecks
