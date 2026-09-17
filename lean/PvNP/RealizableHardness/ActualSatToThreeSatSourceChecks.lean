import PvNP.RealizableHardness.ActualSatToThreeSatSource

/-!
Interface checks for the SAT → encoded-3SAT `SeededMap` with `Preserves (1/6)`.
This file does not inhabit `theorem1_from_threeSat_to_cmmsa` and does not
assert unconditional Theorem 1, Corollary 2, regularized 3-Lin, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSatToThreeSatSourceChecks
open Complexity RandomizedReduction ActualCMMSARandomizedReduction ActualTheorem1
open ActualHeadlineParameters
open PvNP.RealizableHardness.ActualSatToThreeSatSource

#check threeSatSource
#check satToThreeSatMap
#check satToThreeSatMap_apply
#check satToThreeSat_mapReducesVia
#check satToThreeSat_preserves_zero
#check satToThreeSat_preserves
#check satToThreeSat_exists
#check theorem1_from_threeSat_to_cmmsa

#print axioms satToThreeSatMap_apply
#print axioms satToThreeSat_mapReducesVia
#print axioms satToThreeSat_preserves_zero
#print axioms satToThreeSat_preserves
#print axioms satToThreeSat_exists
#print axioms theorem1_from_threeSat_to_cmmsa

noncomputable section

example : satToThreeSatMap.apply [] [] = SAT.ThreeSAT.reduction [] :=
  satToThreeSatMap_apply [] []

example : (PromiseProblem.ofLanguage SAT.language).MapReducesVia
    threeSatSource SAT.ThreeSAT.reduction :=
  satToThreeSat_mapReducesVia

example : RandomizedReduction.Preserves satToThreeSatMap
    (PromiseProblem.ofLanguage SAT.language) threeSatSource 0 0 :=
  satToThreeSat_preserves_zero

example : RandomizedReduction.Preserves satToThreeSatMap
    (PromiseProblem.ofLanguage SAT.language) threeSatSource (1/6) (1/6) :=
  satToThreeSat_preserves

example : ∃ R : RandomizedReduction.SeededMap,
    RandomizedReduction.Preserves R
      (PromiseProblem.ofLanguage SAT.language) threeSatSource (1/6) (1/6) :=
  satToThreeSat_exists

end
end PvNP.RealizableHardness.ActualSatToThreeSatSourceChecks
