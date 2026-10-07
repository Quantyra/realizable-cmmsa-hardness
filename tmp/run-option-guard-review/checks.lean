import PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap

/-!
Interface checks for the selected CMMSA sampling ruler, the packed
decode/`coinRuler` guard of `paddedRunOption`, and the packed
decode/`trials*precision` length guard of `runOption`.
`decodeInputTag_mem_FP` is on the Cobham surface. Remaining gap is
`selectedPairedRun_mem_FP` / `selectedSeededMap`: `checkedBits` / `accepted` /
output `tree` are not packed. This file does not inhabit `hSrcCmmsa` and does
not assert unconditional Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaSeededMapChecks
open Complexity RandomizedReduction
open PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
open PvNP.RealizableHardness.ExecutableSamplingPolicy
open PvNP.RealizableHardness.ExecutablePipelineInput

#check selectedPairedRun
#check selectedCoinRuler
#check selectedCoinRuler_mem_FP
#check paddedRunGuardTag
#check paddedRunGuardTag_mem_FP
#check paddedRunGuardTag_eq
#check paddedRunGuardTag_empty
#check runOptionGuardTag
#check runOptionGuardTag_mem_FP
#check runOptionGuardTag_none
#check runOptionGuardTag_empty

#print axioms selectedCoinRuler_mem_FP
#print axioms paddedRunGuardTag_mem_FP
#print axioms paddedRunGuardTag_eq
#print axioms paddedRunGuardTag_empty
#print axioms runOptionGuardTag_mem_FP
#print axioms runOptionGuardTag_none
#print axioms runOptionGuardTag_empty

example (eps : Rat) (x : List Bool) :
    (selectedCoinRuler eps x).length = coinRuler eps x.length := by
  simp [selectedCoinRuler]

example (L : Nat) : selectedPairedRun L (1/4 : Rat) [] = [] := by
  simp [selectedPairedRun, paddedRun, paddedRunOption, pairFst, pairSnd,
    unpair?, decodeInput_empty]

example (eps : Rat) : selectedCoinRuler eps ∈ Complexity.FP :=
  selectedCoinRuler_mem_FP eps

example (eps : Rat) : paddedRunGuardTag eps ∈ Complexity.FP :=
  paddedRunGuardTag_mem_FP eps

example (eps : Rat) : paddedRunGuardTag eps [] = [] :=
  paddedRunGuardTag_empty eps

example : runOptionGuardTag ∈ Complexity.FP :=
  runOptionGuardTag_mem_FP

example : runOptionGuardTag [] = [] :=
  runOptionGuardTag_empty

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMapChecks
