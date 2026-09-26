import PvNP.RealizableHardness.ActualUnsatPairZeta

/-!
Checks for unsat-pair XOR-star CSP value `1/2` vs list-decoding `rho = 1/8`.
Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualUnsatPairZetaChecks

open PvNP.RealizableHardness.ActualUnsatPairZeta
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.StarListDecoding

#check xorStar
#check xorStar_not_both
#check xorStar_score_le_half
#check eighth_rho_half_zeta
#check eighth_rho_half_zeta_any_arity
#check pairP_sum

example : alph 2 = 16 := rfl

example : ((8 : ℝ) * (1 / 8)) ^ (2 + 1) * ((1 : ℝ) / 2) ≤ (5 : ℝ) / 8 :=
  eighth_rho_half_zeta

#print axioms xorStar_not_both
#print axioms xorStar_score_le_half
#print axioms eighth_rho_half_zeta
#print axioms eighth_rho_half_zeta_any_arity

end PvNP.RealizableHardness.ActualUnsatPairZetaChecks
