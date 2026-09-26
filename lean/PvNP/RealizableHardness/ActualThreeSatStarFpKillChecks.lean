import PvNP.RealizableHardness.ActualThreeSatStarFpKill

/-!
Checks for the FP Grassmann-layout kill. `starEncFn L` stays in
`Complexity.FP` and is not `MapReducesVia` onto the manuscript promise.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarFpKillChecks

open Complexity
open ActualThreeSatStarFpKill
open ActualThreeSatStarFp

set_option autoImplicit false
set_option maxHeartbeats 800000

example (L : Nat) : starEncFn L ∈ FP :=
  starEncFn_mem_FP L

example {L : Nat} (hL : 3 ≤ L) :
    starEncFn L Complexity.SAT.ThreeSAT.falseFormula.encode =
      CMMSACodec.encode
        (CMMSAEncoding.ofData (starKillData L) (starKillData_valid hL)) :=
  starEncFn_falseFormula hL

example {L : Nat} (hL : 3 ≤ L) {sig : Nat} {gam : Rat}
    (hσ : 1 ≤ sig) (hγ : gam ≤ 1) :
    ¬ CMMSACodec.No (sig : Rat) gam
        (CMMSAEncoding.ofData (starKillData L) (starKillData_valid hL)) :=
  starKillData_not_no hL hσ hγ

example {L : Nat} (hL : 3 ≤ L)
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hγ0 : 0 < ActualHeadlineParameters.manuscriptGamma L)
    (hγ1 : ActualHeadlineParameters.manuscriptGamma L < 1) :
    ¬ ActualSatToThreeSatSource.threeSatSource.MapReducesVia
        (ActualCMMSARandomizedReduction.cmmsaPromise L
          (ActualHeadlineParameters.manuscriptSigma L)
          (ActualHeadlineParameters.manuscriptGamma L) hσ hγ0 hγ1)
        (starEncFn L) :=
  starEncFn_not_mapReduces hL hσ hγ0 hγ1

example :
    ∃ L0, ∀ L, L0 ≤ L →
      1 ≤ ActualHeadlineParameters.manuscriptSigma L ∧
        0 < ActualHeadlineParameters.manuscriptGamma L ∧
        ActualHeadlineParameters.manuscriptGamma L < 1 ∧
        ∀ (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
          (hγ0 : 0 < ActualHeadlineParameters.manuscriptGamma L)
          (hγ1 : ActualHeadlineParameters.manuscriptGamma L < 1),
          ¬ ActualSatToThreeSatSource.threeSatSource.MapReducesVia
              (ActualCMMSARandomizedReduction.cmmsaPromise L
                (ActualHeadlineParameters.manuscriptSigma L)
                (ActualHeadlineParameters.manuscriptGamma L) hσ hγ0 hγ1)
              (starEncFn L) :=
  starEncFn_fails_manuscript_eventually

end PvNP.RealizableHardness.ActualThreeSatStarFpKillChecks
