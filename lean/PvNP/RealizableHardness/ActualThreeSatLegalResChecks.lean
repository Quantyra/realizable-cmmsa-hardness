import PvNP.RealizableHardness.ActualThreeSatLegalRes

/-!
Checks for high-bit legal3Lin-filtered Grassmann restriction stars.
Does not inhabit `hSrcCmmsa`.  twoCover remains a cheap covering; not a
`No σ_L γ_L` map.
-/
namespace PvNP.RealizableHardness.ActualThreeSatLegalResChecks

open PvNP.RealizableHardness.ActualThreeSatLegalRes
open PvNP.RealizableHardness.ActualThreeSatGrassmannRes
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.CMMSACodec

#check compileLegal
#check legalHigh
#check legalHigh_zero
#check legalHigh_highBit
#check legalHigh_zero_not_one
#check legalResData
#check legalResData_valid
#check legalResData_yes_unit3
#check unsatCnf_honest_fails_rhs1
#check twoCover_eval
#check legalK_proj_ne_id
#check eval_compileLegal
#check compileLegal_leaves_le

example : alph 3 = 64 := rfl

#print axioms legalResData_valid
#print axioms legalResData_yes_unit3
#print axioms unsatCnf_honest_fails_rhs1
#print axioms twoCover_eval
#print axioms legalK_proj_ne_id
#print axioms eval_compileLegal

end PvNP.RealizableHardness.ActualThreeSatLegalResChecks
