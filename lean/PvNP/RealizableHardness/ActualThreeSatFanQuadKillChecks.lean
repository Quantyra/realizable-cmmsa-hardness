import PvNP.RealizableHardness.ActualThreeSatFanQuadKill

/-!
Checks for the global 4-label witness that `fanData` misses manuscript `No`.
Not `Complexity.FP`.  Does not inhabit Theorem 1.
-/
namespace PvNP.RealizableHardness.ActualThreeSatFanQuadKillChecks

open PvNP.RealizableHardness.ActualThreeSatFanQuadKill
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualThreeSatLegalRes
open PvNP.RealizableHardness.ActualThreeSatGrassmannFan
open PvNP.RealizableHardness.CMMSACodec hiding Tree
open PvNP.RealizableHardness.CMMSAEncoding
open Complexity.SAT

#check fanData_not_no_manuscript
#check fanData_fails_manuscript_eventually

example {L : Nat} (h : 256 ≤ mOf L) (hh : 3 < legalH L)
    (h4 : 4 ≤ manuscriptSigma L) (hγ1 : manuscriptGamma L < 1) :
    ¬ No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (fanData hh (paramM_ge_3 h) unsatCnf unsatCnf_is3
          (by decide : 0 < unsatCnf.length))
        (fanData_valid h hh unsatCnf unsatCnf_is3
          (by decide : 0 < unsatCnf.length))) :=
  fanData_not_no_manuscript h hh h4 hγ1 unsatCnf unsatCnf_is3
    (by decide : 0 < unsatCnf.length)

#print axioms fanData_not_no_manuscript
#print axioms fanData_fails_manuscript_eventually

end PvNP.RealizableHardness.ActualThreeSatFanQuadKillChecks
