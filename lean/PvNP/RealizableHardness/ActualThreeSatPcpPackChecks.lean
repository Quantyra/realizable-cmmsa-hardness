import PvNP.RealizableHardness.ActualThreeSatPcpPack

/-!
Checks for the 3SAT-dependent polarity-OR packing and the cheap witnesses
that polarity-OR / XOR-star families are not `No`.

Does not inhabit `hSrcCmmsa`.  Polarity-OR and XOR-star packings miss
manuscript `No` for large `L`.  Not `Complexity.FP`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatPcpPackChecks

open PvNP.RealizableHardness.ActualThreeSatPcpPack
open PvNP.RealizableHardness.ActualHeadlineParameters
open PvNP.RealizableHardness.ActualThreeSatStarFamily
open PvNP.RealizableHardness.ActualThreeSatXorStars
open PvNP.RealizableHardness.ActualThreeSatGraphYes
open PvNP.RealizableHardness.CMMSACodec hiding Tree
open PvNP.RealizableHardness.CMMSAEncoding
open Complexity.SAT

#check threeSatToStarBits
#check threeSatToStarBits_yes_of_sat
#check threeSatToStarBits_ne_id
#check paramStarData_not_no
#check twoLabel
#check xorStarData_not_no
#check paramStarData_not_no_manuscript
#check xorStarData_not_no_manuscript
#check manyValuedPackings_fail_manuscript_eventually

example {L : Nat} (h : 256 ≤ mOf L) :
    threeSatToStarBits h satUnit satUnit_is3 satUnit_len ≠ [] :=
  threeSatToStarBits_ne_id h

example {L : Nat} (h : 256 ≤ mOf L) (hσ : 1 ≤ manuscriptSigma L)
    (hγ1 : manuscriptGamma L < 1) :
    ¬ No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (paramStarData L satUnit satUnit_is3 satUnit_len)
        (paramStarData_valid h satUnit satUnit_is3 satUnit_len)) :=
  paramStarData_not_no_manuscript h hσ hγ1 satUnit satUnit_is3 satUnit_len

example {L : Nat} (h : 256 ≤ mOf L) (hh : 0 < hOf L (mOf L))
    (h2 : 2 ≤ manuscriptSigma L) (hγ1 : manuscriptGamma L < 1) :
    ¬ No (manuscriptSigma L) (manuscriptGamma L)
      (ofData (xorStarData (h := hOf L (mOf L)) hh satUnit satUnit_is3 satUnit_len)
        (xorStarData_valid_of_mOf h hh satUnit satUnit_is3 satUnit_len)) :=
  xorStarData_not_no_manuscript h hh h2 hγ1 satUnit satUnit_is3 satUnit_len

#print axioms threeSatToStarBits_yes_of_sat
#print axioms threeSatToStarBits_ne_id
#print axioms paramStarData_not_no
#print axioms xorStarData_not_no
#print axioms paramStarData_not_no_manuscript
#print axioms xorStarData_not_no_manuscript
#print axioms manyValuedPackings_fail_manuscript_eventually

end PvNP.RealizableHardness.ActualThreeSatPcpPackChecks
