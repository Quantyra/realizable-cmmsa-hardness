import PvNP.RealizableHardness.ActualSelectedCmmsaPaddedRunFracFP
import PvNP.RealizableHardness.RandomizedReduction

/-!
FP `SeededMap` whose run is the packed frac padded-run tag.

`selectedPairedRun_mem_FP` / `paddedRunOutputTag_mem_FP` name the packed
executor already shown to lie in `Complexity.FP`.  They do not unfold to
`selectedPairedRun` or `CMMSACodec.accepted`.  This module does not inhabit
`hSrcCmmsa` and does not prove unconditional Theorem 1, Corollary 2, or
P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaSelectedMapFP

open Complexity
open RandomizedReduction
open ActualSelectedCmmsaPaddedRunFracFP
open ActualSelectedCmmsaSeededMap
open ExecutableSamplingPolicy
set_option autoImplicit false

theorem paddedRunOutputTag_mem_FP (L : Nat) (eps : Rat) :
    packedFracPaddedRunOutputTag L eps ∈ Complexity.FP :=
  packedFracPaddedRunOutputTag_mem_FP L eps

theorem selectedPairedRun_mem_FP (L : Nat) (eps : Rat) :
    packedFracPaddedRunOutputTag L eps ∈ Complexity.FP :=
  packedFracPaddedRunOutputTag_mem_FP L eps

noncomputable def selectedSeededMap (L : Nat) (eps : Rat) :
    RandomizedReduction.SeededMap where
  run := packedFracPaddedRunOutputTag L eps
  run_fp := packedFracPaddedRunOutputTag_mem_FP L eps
  ruler := selectedCoinRuler eps
  ruler_fp := selectedCoinRuler_mem_FP eps
  coinCount := fun n => coinRuler eps n
  ruler_length := fun x => by
    simp [selectedCoinRuler, List.length_replicate]

end PvNP.RealizableHardness.ActualSelectedCmmsaSelectedMapFP
