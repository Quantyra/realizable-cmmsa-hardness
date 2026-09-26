import PvNP.RealizableHardness.ActualThreeSatBruteMap

namespace PvNP.RealizableHardness.ActualThreeSatBruteMapChecks

open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatBruteMap
open ActualThreeSatToCmmsa

example {L : Nat} (h : 256 ≤ mOf L) :
    bruteEnc L h [] = yesBits (L_pos_of_mOf h) :=
  bruteEnc_yes_of_nil h

example {L : Nat} (h : 256 ≤ mOf L) :
    bruteEnc L h falseFormula.encode = noBits (L_pos_of_mOf h) :=
  bruteEnc_no_of_falseFormula h

example {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    threeSatSource.MapReducesVia
      (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) (bruteEnc L h) :=
  bruteEnc_mapReducesVia h hσ hγ0 hγ1

example {L : Nat} (hL : 0 < L) (hσ : 1 ≤ rofSigma L) :
    yesBits hL ≠ noBits hL :=
  yesBits_ne_noBits hL hσ

example {L : Nat} (h : 256 ≤ mOf L) (hσ : 1 ≤ rofSigma L) (z : List Bool) :
    bruteEnc L h z = yesBits (L_pos_of_mOf h) ↔ z ∈ ThreeSAT.language :=
  bruteEnc_eq_yesBits_iff h hσ z

example {L : Nat} (h : 256 ≤ mOf L) (hσ : 1 ≤ rofSigma L)
    (hf : bruteEnc L h ∈ FP) :
    ThreeSAT.language ∈ P :=
  threeSat_in_P_of_bruteEnc_mem_FP h hσ hf

end PvNP.RealizableHardness.ActualThreeSatBruteMapChecks
