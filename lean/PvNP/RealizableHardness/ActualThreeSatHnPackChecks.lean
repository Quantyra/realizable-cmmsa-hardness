import PvNP.RealizableHardness.ActualThreeSatHnPack

/-!
Checks for HN 1-hot completeness of XOR-star `Data`.
Does not inhabit `hSrcCmmsa`.  2-leaf XOR is not a No-map at `σ_L`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatHnPackChecks

open PvNP.RealizableHardness.ActualThreeSatHnPack
open PvNP.RealizableHardness.ActualThreeSatXorStars
open PvNP.RealizableHardness.ActualThreeSatGraphYes
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualBitRestriction
open PvNP.RealizableHardness.ActualCompactStarCompile
open PvNP.RealizableHardness.CMMSACodec

#check labelOneHot
#check labelOneHot_coord
#check labelOneHot_cost
#check eval_clauseXor_labelOneHot
#check xorStarData_yes_of_labeling
#check xorStarData_yes_satUnit
#check xorStarData_yes_satUnit_mem
#check hn_rofSigma_arity2
#check zero_zeta_arity2_hn
#check three_quarters_lt_four_fifths

example : alph 2 = 16 := rfl

example : (3 / 4 : Rat) < (4 / 5 : Rat) :=
  three_quarters_lt_four_fifths

example {L : Nat} (hσ : 0 < rofSigma L) :
    ((8 : Rat) * (rofSigma L : Rat)) ^ (2 + 1) * (0 : Rat) ≤ (5 : Rat) / 8 :=
  zero_zeta_arity2_hn hσ

#print axioms labelOneHot_cost
#print axioms eval_clauseXor_labelOneHot
#print axioms xorStarData_yes_of_labeling
#print axioms xorStarData_yes_satUnit
#print axioms xorStarData_yes_satUnit_mem
#print axioms hn_rofSigma_arity2
#print axioms zero_zeta_arity2_hn
#print axioms three_quarters_lt_four_fifths

end PvNP.RealizableHardness.ActualThreeSatHnPackChecks
