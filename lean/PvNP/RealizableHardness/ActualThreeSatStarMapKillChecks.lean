import PvNP.RealizableHardness.ActualThreeSatRofNo
import PvNP.RealizableHardness.ActualThreeSatStarMapKill

namespace PvNP.RealizableHardness.ActualThreeSatStarMapKillChecks

open Complexity
open Complexity.SAT.ThreeSAT
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatPcpPack
open ActualThreeSatRofNo
open ActualThreeSatStarMapKill

example {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1)
        (fun _ => threeSatToStarBits h falseFormula falseFormula_is3CNF
          falseFormula_pos) := by
  apply starBits_blocks_mapReducesVia h hσ hγ0 hγ1
  rfl

example {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (h8 : 8 ≤ ROf L) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) (rofNoEnc L h) :=
  rofNoEnc_not_mapReduces h hσ hγ0 hγ1 h8

end PvNP.RealizableHardness.ActualThreeSatStarMapKillChecks
