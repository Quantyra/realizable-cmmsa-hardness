import PvNP.RealizableHardness.ActualThreeSatUniformCompile
import PvNP.RealizableHardness.ActualThreeSatUniformEncKill

namespace PvNP.RealizableHardness.ActualThreeSatUniformEncKillChecks

open Complexity
open Complexity.SAT.ThreeSAT
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualSatToThreeSatSource
open ActualThreeSatUniformCompile
open ActualThreeSatUniformEncKill

/-- The shipped `uniformEnc` is not a 3SAT to `cmmsaPromise` many-one map. -/
example {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ rofSigma L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1) :
    ¬ threeSatSource.MapReducesVia
        (cmmsaPromise L (rofSigma L) (gammaL L) hσ hγ0 hγ1) (uniformEnc L h) :=
  uniformEnc_not_mapReduces h hσ hγ0 hγ1

end PvNP.RealizableHardness.ActualThreeSatUniformEncKillChecks
