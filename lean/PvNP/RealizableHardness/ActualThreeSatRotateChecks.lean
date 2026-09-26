import PvNP.RealizableHardness.ActualThreeSatRotate

/-!
Checks for triple-chart rotate packing.  `fourCover` and cheaper
vertex-dependent `{0,2^h}` dummy 2-hot fail RHS-1.  Remaining 7-hot
still covers: not `No σ_L γ_L`, not `hSrcCmmsa`.  Not `compileOverlap` /
`fourCover` / `vdCover` / `compileMid`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatRotateChecks

open PvNP.RealizableHardness.ActualThreeSatRotate
open PvNP.RealizableHardness.ActualThreeSatOverlap
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.CMMSACodec

#check restrictRot
#check restrictRot_ne_id
#check restrictRot_dualBit
#check compileRotate
#check eval_compileRotate
#check fourCover_not_eval_rhs1
#check fourCover_not_eval_unsatCnf
#check cheapTwo_not_eval_rhs1
#check cheapTwo_not_eval_unsatCnf
#check sevenCover_eval_rhs1
#check rotData_valid
#check rotData_yes_unit3
#check rotEncFn
#check rotEncFn_mem_FP
#check rotEncFn_ne_id

example : alph 3 = 64 := rfl

#print axioms eval_compileRotate
#print axioms restrictRot_dualBit
#print axioms fourCover_not_eval_rhs1
#print axioms cheapTwo_not_eval_rhs1
#print axioms sevenCover_eval_rhs1
#print axioms rotData_yes_unit3
#print axioms rotEncFn_mem_FP
#print axioms restrictRot_ne_id

end PvNP.RealizableHardness.ActualThreeSatRotateChecks
