import PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap

/-!
Interface checks for the selected CMMSA sampling ruler and the packed
decode/`coinRuler` guard of `paddedRunOption`. `decodeInputTag_mem_FP` is now
on the Cobham surface. Remaining gap is `selectedPairedRun_mem_FP` /
`selectedSeededMap`: `runOption` / `checkedBits` / `accepted` / output `tree`
are not packed. This file does not inhabit `hSrcCmmsa` and does not assert
unconditional Theorem 1, Corollary 2, or P vs NP.
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

#print axioms selectedCoinRuler_mem_FP
#print axioms paddedRunGuardTag_mem_FP
#print axioms paddedRunGuardTag_eq
#print axioms paddedRunGuardTag_empty

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

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMapChecks
