import PvNP.RealizableHardness.ActualTheorem1

/-!
Interface checks for the Cook–Levin zero-coin lift and the two-stage
`Preserves (1/6)` Theorem 1 route. This file does not inhabit
`theorem1_realizable_cmmsa` and does not assert Corollary 2 or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualTheorem1Checks
open Complexity RandomizedReduction
open PvNP.RealizableHardness.ActualTheorem1
open PvNP.RealizableHardness.ActualCMMSARandomizedReduction

#check fpSeededMap
#check fpSeededMap_apply
#check fpSeededMap_coinCount
#check fpSeededMap_preserves
#check np_to_sat_seeded
#check theorem1_realizable_cmmsa

#print axioms fpSeededMap_apply
#print axioms fpSeededMap_coinCount
#print axioms fpSeededMap_preserves
#print axioms np_to_sat_seeded
#print axioms theorem1_realizable_cmmsa

noncomputable section

example : (fpSeededMap id id_mem_FP).coinCount 0 = 0 :=
  fpSeededMap_coinCount id id_mem_FP 0

example : (fpSeededMap id id_mem_FP).apply [true, false] [true] = [true, false] :=
  fpSeededMap_apply id id_mem_FP _ _

example : (fpSeededMap id id_mem_FP).apply [] [] = [] :=
  fpSeededMap_apply id id_mem_FP [] []

example : ∃ R : RandomizedReduction.SeededMap,
    RandomizedReduction.Preserves R
      (PromiseProblem.ofLanguage SAT.language)
      (PromiseProblem.ofLanguage SAT.language) 0 0 :=
  np_to_sat_seeded SAT.language_mem_NP

example : ∃ R : RandomizedReduction.SeededMap,
    RandomizedReduction.Preserves R
      (PromiseProblem.ofLanguage SAT.language)
      (PromiseProblem.ofLanguage SAT.language) 0 0 :=
  np_to_sat_seeded SAT.NPComplete_language.1

end
end PvNP.RealizableHardness.ActualTheorem1Checks
