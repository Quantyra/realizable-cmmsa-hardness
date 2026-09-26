import PvNP.RealizableHardness.ActualThreeSatHalfWidth

/-!
Checks for half-width DualWindow (`k = h`).  DualWindow leftover
`{0, 1+2^h}` fails RHS-1.  Every spatially constant 2-label palette fails
mixed RHS.  Remaining 3-hot `{0, 1, 1+2^h}` still covers: not `No σ_L γ_L`,
not `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatHalfWidthChecks

open PvNP.RealizableHardness.ActualThreeSatHalfWidth
open PvNP.RealizableHardness.ActualThreeSatDualWindow
open PvNP.RealizableHardness.ActualThreeSatLegalRes
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.CMMSACodec

#check compileMid
#check eval_compileMid
#check midK_proj_ne_id
#check restrictLow_dualBit_eq_one
#check dualCover_not_eval_rhs1
#check dualCover_not_eval_unsatCnf
#check twoHot_not_both_rhs
#check threeCover_eval_rhs1
#check threeCover_eval_unsatCnf_rhs1
#check midResData
#check midResData_valid
#check midResData_yes_unit3
#check midEncFn
#check midEncFn_mem_FP
#check midEncFn_ne_id

example : alph 3 = 64 := rfl
example : midK 3 = 3 := rfl

#print axioms eval_compileMid
#print axioms restrictLow_dualBit_eq_one
#print axioms dualCover_not_eval_rhs1
#print axioms twoHot_not_both_rhs
#print axioms threeCover_eval_rhs1
#print axioms midResData_yes_unit3
#print axioms midEncFn_mem_FP
#print axioms midK_proj_ne_id

end PvNP.RealizableHardness.ActualThreeSatHalfWidthChecks
