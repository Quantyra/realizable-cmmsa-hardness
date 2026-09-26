import PvNP.RealizableHardness.ActualThreeSatXorStars

/-!
Checks for 3SAT-dependent XOR stars at `ROf L`.
Does not inhabit `hSrcCmmsa` and does not claim unsat zeta meets
`hn_zeta_beats_sigma`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatXorStarsChecks

open PvNP.RealizableHardness.ActualThreeSatXorStars
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.ActualUnsatPairZeta

#check eight_mul_rofSigma_eq_ROf
#check clauseXorFormula
#check clauseXorFormula_leaves
#check xorStarData_valid
#check xorStarData_valid_of_mOf
#check hn_zeta_beats_ROf
#check eighth_rho_half_zeta

example : alph 2 = 16 := rfl

#print axioms eight_mul_rofSigma_eq_ROf
#print axioms clauseXorFormula_leaves
#print axioms xorStarData_valid
#print axioms hn_zeta_beats_ROf

end PvNP.RealizableHardness.ActualThreeSatXorStarsChecks
