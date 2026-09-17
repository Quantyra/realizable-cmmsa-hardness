import PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap

/-!
Interface checks for the selected CMMSA sampling ruler. `selectedSeededMap`
is not defined: `selectedPairedRun_mem_FP` is blocked by the missing Cobham
parser lemmas for `paddedRun`/`decodeInput`/`Tree.parse`. This file does not
inhabit `hSrcCmmsa` and does not assert unconditional Theorem 1, Corollary 2,
or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaSeededMapChecks
open Complexity RandomizedReduction
open PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
open PvNP.RealizableHardness.ExecutableSamplingPolicy
open PvNP.RealizableHardness.ExecutablePipelineInput

#check selectedPairedRun
#check selectedCoinRuler
#check selectedCoinRuler_mem_FP

#print axioms selectedCoinRuler_mem_FP

example (eps : Rat) (x : List Bool) :
    (selectedCoinRuler eps x).length = coinRuler eps x.length := by
  simp [selectedCoinRuler]

example (L : Nat) : selectedPairedRun L (1/4 : Rat) [] = [] := by
  simp [selectedPairedRun, paddedRun, paddedRunOption, pairFst, pairSnd,
    unpair?, decodeInput_empty]

example (eps : Rat) : selectedCoinRuler eps ∈ Complexity.FP :=
  selectedCoinRuler_mem_FP eps

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMapChecks
