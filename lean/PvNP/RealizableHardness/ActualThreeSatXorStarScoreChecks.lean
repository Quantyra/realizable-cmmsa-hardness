import PvNP.RealizableHardness.ActualThreeSatXorStarScore

/-!
Checks for 3SAT-dependent XOR `Star`s and the HN bound at `zeta = 0`.
Does not inhabit `hSrcCmmsa`.  3SAT-unsat is not proved to imply `xorUnsat`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatXorStarScoreChecks

open PvNP.RealizableHardness.ActualThreeSatXorStarScore
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction

#check clauseXorStar
#check xorUnsat
#check zero_zeta_meets_hn
#check zero_zeta_le_hn_premise
#check zero_zeta_hn_zeta_beats_sigma

example : alph 2 = 16 := rfl

example {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (mOf L + 1) * (0 : Rat) ≤ (5 : Rat) / 8 :=
  zero_zeta_hn_zeta_beats_sigma hσ

#print axioms zero_zeta_meets_hn
#print axioms zero_zeta_hn_zeta_beats_sigma
#print axioms zero_zeta_le_hn_premise

end PvNP.RealizableHardness.ActualThreeSatXorStarScoreChecks
