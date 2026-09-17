import PvNP.RealizableHardness.ActualHeadlineParameters
import Complexitylib.SAT.ThreeSAT.Completeness

/-!
Proved SAT → encoded-3SAT Karp reduction as a zero-coin then `1/6`
`SeededMap`. Source is `ofLanguage ThreeSAT.language`, not regularized
3-Lin. This module does not inhabit 3SAT → `cmmsaPromise` and does not
prove unconditional Theorem 1, Corollary 2, or P vs NP.
-/
namespace PvNP.RealizableHardness.ActualSatToThreeSatSource
open Complexity RandomizedReduction ActualCMMSARandomizedReduction ActualTheorem1
open ActualHeadlineParameters

def threeSatSource : PromiseProblem :=
  PromiseProblem.ofLanguage Complexity.SAT.ThreeSAT.language

noncomputable def satToThreeSatMap : RandomizedReduction.SeededMap :=
  fpSeededMap Complexity.SAT.ThreeSAT.reduction
    Complexity.SAT.ThreeSAT.reduction_mem_FP

theorem satToThreeSatMap_apply (x seed : List Bool) :
    satToThreeSatMap.apply x seed = Complexity.SAT.ThreeSAT.reduction x :=
  fpSeededMap_apply Complexity.SAT.ThreeSAT.reduction
    Complexity.SAT.ThreeSAT.reduction_mem_FP x seed

theorem satToThreeSat_mapReducesVia :
    (PromiseProblem.ofLanguage Complexity.SAT.language).MapReducesVia
      threeSatSource Complexity.SAT.ThreeSAT.reduction := by
  constructor
  · intro z hz
    exact (SAT.ThreeSAT.mem_language_iff_reduction_mem z).mp hz
  · intro z hz
    exact mt (SAT.ThreeSAT.mem_language_iff_reduction_mem z).mpr hz

theorem satToThreeSat_preserves_zero :
    RandomizedReduction.Preserves satToThreeSatMap
      (PromiseProblem.ofLanguage Complexity.SAT.language) threeSatSource 0 0 :=
  fpSeededMap_preserves Complexity.SAT.ThreeSAT.reduction
    Complexity.SAT.ThreeSAT.reduction_mem_FP _ _ satToThreeSat_mapReducesVia

theorem satToThreeSat_preserves :
    RandomizedReduction.Preserves satToThreeSatMap
      (PromiseProblem.ofLanguage Complexity.SAT.language) threeSatSource (1/6) (1/6) :=
  preserves_mono satToThreeSat_preserves_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem satToThreeSat_exists :
    ∃ R : RandomizedReduction.SeededMap,
      RandomizedReduction.Preserves R
        (PromiseProblem.ofLanguage Complexity.SAT.language) threeSatSource (1/6) (1/6) :=
  ⟨satToThreeSatMap, satToThreeSat_preserves⟩

/-- Theorem 1 at σ_L, γ_L, needing only 3SAT → cmmsaPromise Preserves (1/6). -/
theorem theorem1_from_threeSat_to_cmmsa
    {L : Nat}
    (hσ : 1 ≤ sigmaL L) (hγ0 : 0 < gammaL L) (hγ1 : gammaL L < 1)
    (hSrcCmmsa : ∃ S : RandomizedReduction.SeededMap,
      RandomizedReduction.Preserves S threeSatSource
        (cmmsaPromise L (sigmaL L) (gammaL L) hσ hγ0 hγ1) (1/6) (1/6)) :
    RandomizedPromiseNPHard (cmmsaPromise L (sigmaL L) (gammaL L) hσ hγ0 hγ1) :=
  theorem1_headline hσ hγ0 hγ1 threeSatSource satToThreeSat_exists hSrcCmmsa

end PvNP.RealizableHardness.ActualSatToThreeSatSource
