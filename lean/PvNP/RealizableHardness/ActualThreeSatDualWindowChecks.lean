import PvNP.RealizableHardness.ActualThreeSatDualWindow

/-!
Checks for dual-window compileBoth.  `{0,1}` and `{0,2^h}` fail RHS-1.
Remaining cover `{0, 1+2^h}` is still cheap: not `No σ_L γ_L`, not
`hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatDualWindowChecks

open PvNP.RealizableHardness.ActualThreeSatDualWindow
open PvNP.RealizableHardness.ActualThreeSatLegalRes
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction

#check compileBoth
#check eval_compileBoth
#check legalBoth_zero
#check legalBoth_dualBit
#check legalBoth_lowOne_not_one
#check legalBoth_highBit_not_one
#check twoCover_not_eval_rhs1
#check twoCover_not_eval_unsatCnf
#check oneCover_not_eval_rhs1
#check oneCover_not_eval_unsatCnf
#check bothEncFn_mem_FP
#check bothEncFn_ne_id

example : alph 3 = 64 := rfl

#print axioms eval_compileBoth
#print axioms twoCover_not_eval_rhs1
#print axioms oneCover_not_eval_rhs1
#print axioms bothEncFn_mem_FP
#print axioms legalBoth_dualBit

end PvNP.RealizableHardness.ActualThreeSatDualWindowChecks
