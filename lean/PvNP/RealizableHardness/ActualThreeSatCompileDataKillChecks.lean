import PvNP.RealizableHardness.ActualThreeSatCompileDataKill

/-!
Checks for the FP clause-0 compiler kill. `encodeCompileFn` stays in
`Complexity.FP` and is not `MapReducesVia` onto the manuscript promise.
-/
namespace PvNP.RealizableHardness.ActualThreeSatCompileDataKillChecks

open Complexity
open ActualThreeSatCompileDataKill
open ActualThreeSatCompileDataFp

set_option autoImplicit false
set_option maxHeartbeats 800000

example : encodeCompileFn ∈ FP :=
  encodeCompileFn_mem_FP

example (p : Nat) (hp : p < 3) :
    ActualThreeSatLitVarFp.clauseLitVarFn 0 p
        Complexity.SAT.ThreeSAT.falseFormula.encode = [] :=
  clauseLitVarFn_falseFormula p hp

example :
    ActualThreeSatClauseOrFp.clauseOrEnc
        Complexity.SAT.ThreeSAT.falseFormula.encode =
      CMMSACodec.Tree.encode (CMMSAEncoding.formulaTree polarityOr) :=
  clauseOrEnc_falseFormula

example {L : Nat} (hL : 3 ≤ L) :
    encodeCompileFn Complexity.SAT.ThreeSAT.falseFormula.encode =
      CMMSACodec.encode (CMMSAEncoding.ofData killData (killData_valid hL)) :=
  encodeCompileFn_falseFormula hL

example {L : Nat} (hL : 3 ≤ L) {sig : Nat} {gam : Rat}
    (hσ : 2 ≤ sig) (hγ : gam ≤ 1) :
    ¬ CMMSACodec.No (sig : Rat) gam
        (CMMSAEncoding.ofData killData (killData_valid hL)) :=
  killData_not_no hL hσ hγ

example {L : Nat} (hL : 3 ≤ L)
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hγ0 : 0 < ActualHeadlineParameters.manuscriptGamma L)
    (hγ1 : ActualHeadlineParameters.manuscriptGamma L < 1)
    (h2 : 2 ≤ ActualHeadlineParameters.manuscriptSigma L) :
    ¬ ActualSatToThreeSatSource.threeSatSource.MapReducesVia
        (ActualCMMSARandomizedReduction.cmmsaPromise L
          (ActualHeadlineParameters.manuscriptSigma L)
          (ActualHeadlineParameters.manuscriptGamma L) hσ hγ0 hγ1)
        encodeCompileFn :=
  encodeCompileFn_not_mapReduces hL hσ hγ0 hγ1 h2

end PvNP.RealizableHardness.ActualThreeSatCompileDataKillChecks
