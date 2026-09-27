import PvNP.RealizableHardness.ActualGapPowerBelowGamma

namespace PvNP.RealizableHardness.ActualGapPowerBelowGammaChecks

open ActualGapPowerBelowGamma
open Complexity
open Dinur

example (k : Nat) : ((1 : Rat) / 2) ^ k ≤ 4 * ((3 : Rat) / 4) ^ k :=
  half_pow_le_four_mul_three_quarters k

example (F : FinBase) (hd : 1 < F.deg) :
    ∃ L0, ∀ L, L0 ≤ L →
      (1 - (amplifier (F.toFamily hd)).gap) ^ L <
        ActualHeadlineParameters.manuscriptGamma L :=
  gap_leaf_power_lt_manuscriptGamma F hd

#print axioms half_pow_le_four_mul_three_quarters
#print axioms gap_leaf_power_lt_manuscriptGamma

end PvNP.RealizableHardness.ActualGapPowerBelowGammaChecks
