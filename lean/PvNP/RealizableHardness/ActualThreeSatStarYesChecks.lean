import PvNP.RealizableHardness.ActualThreeSatStarYes

/-!
Checks for Grassmann 1-clause polarity-OR `Yes 0` and not-No.
Does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatStarYesChecks

open PvNP.RealizableHardness.ActualThreeSatStarYes
open PvNP.RealizableHardness.ActualThreeSatStarFp
open PvNP.RealizableHardness.CMMSACodec
open PvNP.RealizableHardness.CMMSAEncoding
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualCompactStarCompile

#check unitStarData
#check unitStarData_valid
#check unitStarData_yes
#check unitStarData_not_no
#check unitStarData_yes_mem
#check starEncFn_mem_FP

example {L : Nat} (hL : 3 ≤ L) :
    Yes 0 (ofData (unitStarData L) (unitStarData_valid hL)) :=
  unitStarData_yes hL

example {L : Nat} (hL : 3 ≤ L) (hσ : 1 ≤ rofSigma L) (hγ1 : gammaL L < 1) :
    ¬ No (rofSigma L) (gammaL L)
      (ofData (unitStarData L) (unitStarData_valid hL)) :=
  unitStarData_not_no hL hσ hγ1

#print axioms unitStarData_yes
#print axioms unitStarData_not_no
#print axioms unitStarData_yes_mem
#print axioms unitStarData_valid

end PvNP.RealizableHardness.ActualThreeSatStarYesChecks
