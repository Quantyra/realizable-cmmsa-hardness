import PvNP.RealizableHardness.ActualManyWDecoderGameJoin

namespace PvNP.RealizableHardness.ActualManyWDecoderGameJoinChecks

open PvNP.RealizableHardness.ActualManyWDecoderGameJoin
open PvNP.RealizableHardness.ActualMZ24D3c5Precomposition

#check sixteen_factor_of_list_card
#check manyW_decoder_repeatedGame_join

/-- A fibre of size 4 at agreement 1 is inside `16 / 1^2`, so the uniform
hit probability is at least `1/16`. -/
example : (1 : ℚ) ^ 2 / 16 ≤ 1 / (4 : ℚ) := by
  exact sixteen_factor_of_list_card (by norm_num) (by decide : 0 < 4)
    (by norm_num : (4 : ℚ) ≤ 16 / (1 : ℚ) ^ 2)

/-- The bound is tight at a full list of size 16. -/
example : (1 : ℚ) ^ 2 / 16 ≤ 1 / (16 : ℚ) := by
  exact sixteen_factor_of_list_card (by norm_num) (by decide : 0 < 16)
    (by norm_num : (16 : ℚ) ≤ 16 / (1 : ℚ) ^ 2)

/-- The join still uses the frozen ledger arithmetic, not a smaller cap. -/
example : 50 * 2 * 302 * 1 ^ 5 + L6 2 302 2 1 1 ≤ Ecap 1 2 2 302 := by
  norm_num [Ecap, L6, L5]

example : ¬ 50 * 1 * 1 * 1 + L6 1 1 1 1 0 ≤ Ecap 1 1 1 1 := by
  norm_num [Ecap, L6, L5]

end PvNP.RealizableHardness.ActualManyWDecoderGameJoinChecks
