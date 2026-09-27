import Complexitylib.Classes.PCP.Internal.AlgPCP
import PvNP.RealizableHardness.ActualDinurGapHalf

/-!
Checks for Dinur's half-gap and the matching-arity HN miss.
-/
namespace PvNP.RealizableHardness.ActualDinurGapHalfChecks

open Complexity
open ActualDinurGapHalf

#check dinur_powFloor_le_half
#check dinur_gap_le_half
#check one_sub_dinur_gap_ge_half
#check dinur_power_ceiling_misses_hn

example (E : ExpanderFamily) : Dinur.gap₀ E ≤ (1 : Rat) / 2 :=
  dinur_gap_le_half E

example :
    ∃ L0, ∀ L, L0 ≤ L → ∀ t : ℕ,
      ¬ ((8 * (ActualHeadlineParameters.manuscriptSigma L : Rat)) ^ (t + 1) *
            (1 - (Dinur.amplifier (algF.toFamily algHd)).gap) ^ t ≤
          (5 : Rat) / 8) :=
  dinur_power_ceiling_misses_hn (algF.toFamily algHd)

#print axioms dinur_gap_le_half
#print axioms dinur_power_ceiling_misses_hn

end PvNP.RealizableHardness.ActualDinurGapHalfChecks
