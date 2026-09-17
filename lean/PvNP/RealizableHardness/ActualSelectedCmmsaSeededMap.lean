import PvNP.RealizableHardness.ActualSatToThreeSatSource
import PvNP.RealizableHardness.ExecutableSamplingPolicy
import Complexitylib.Classes.P.Cobham
import Complexitylib.Classes.P.Cobham.Internal

/-!
Selected sampling `coinRuler` as an FP length ruler, and the paired `paddedRun`
executor. `selectedPairedRun_mem_FP` is omitted: `paddedRun`, `decodeInput`,
and `Tree.parse` are not on the Cobham FP surface, so `selectedSeededMap` is
not defined. This module does not inhabit `hSrcCmmsa`, does not use a dummy
3SAT→CMMSA identity, and does not prove unconditional Theorem 1, Corollary 2,
or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
open Complexity RandomizedReduction ActualHeadlineParameters
open ActualSatToThreeSatSource ExecutableSamplingPolicy

def selectedPairedRun (L : Nat) (eps : Rat) : List Bool → List Bool :=
  fun z => ExecutableSamplingPolicy.paddedRun L eps
    (Complexity.pairFst z) (Complexity.pairSnd z)

def selectedCoinRuler (eps : Rat) : List Bool → List Bool :=
  fun x => List.replicate (ExecutableSamplingPolicy.coinRuler eps x.length) false

private theorem squareRuler_mem_FP :
    (fun x : List Bool => List.replicate ((id x).length * (id x).length) false) ∈ FP :=
  Cobham.mulLenFn_mem_FP id_mem_FP id_mem_FP

private theorem linearRuler_mem_FP :
    (fun x : List Bool =>
      List.replicate ((List.replicate 11 false).length * (id x).length) false) ∈ FP :=
  Cobham.mulLenFn_mem_FP (Cobham.const_replicate_mem_FP 11) id_mem_FP

private theorem quadraticRuler_mem_FP :
    (fun x : List Bool =>
      List.replicate ((id x).length * (id x).length) false ++
        List.replicate ((List.replicate 11 false).length * (id x).length) false) ∈ FP :=
  Cobham.appendFn_mem_FP squareRuler_mem_FP linearRuler_mem_FP

theorem selectedCoinRuler_mem_FP (eps : Rat) :
    selectedCoinRuler eps ∈ Complexity.FP := by
  have hscaled :
      (fun x : List Bool =>
        List.replicate
          ((List.replicate (512 * inverseCeil eps ^ 3) false).length *
            (List.replicate ((id x).length * (id x).length) false ++
              List.replicate ((List.replicate 11 false).length * (id x).length)
                false).length)
          false) ∈ FP :=
    Cobham.mulLenFn_mem_FP
      (Cobham.const_replicate_mem_FP (512 * inverseCeil eps ^ 3))
      quadraticRuler_mem_FP
  have heq :
      (fun x : List Bool =>
        List.replicate
          ((List.replicate (512 * inverseCeil eps ^ 3) false).length *
            (List.replicate ((id x).length * (id x).length) false ++
              List.replicate ((List.replicate 11 false).length * (id x).length)
                false).length)
          false) =
        selectedCoinRuler eps := by
    funext x
    simp only [selectedCoinRuler, id_eq, List.length_replicate, List.length_append]
    rw [coinRuler_quadratic, Nat.pow_two]
  rwa [heq] at hscaled

end PvNP.RealizableHardness.ActualSelectedCmmsaSeededMap
