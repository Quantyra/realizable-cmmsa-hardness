import PvNP.RealizableHardness.ActualThreeSatManuscriptBruteKill

/-!
Checks for the manuscript two-valued map. It is `MapReducesVia`, its
no-images have budget `< 1/σ`, and an `FP` proof would put 3SAT in `P`.
-/
namespace PvNP.RealizableHardness.ActualThreeSatManuscriptBruteKillChecks

open ActualThreeSatManuscriptBruteKill

set_option autoImplicit false
set_option maxHeartbeats 800000

example {L : Nat} (h : 256 ≤ ActualHeadlineParameters.mOf L)
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hγ0 : 0 < ActualHeadlineParameters.manuscriptGamma L)
    (hγ1 : ActualHeadlineParameters.manuscriptGamma L < 1) :
    ActualSatToThreeSatSource.threeSatSource.MapReducesVia
      (ActualCMMSARandomizedReduction.cmmsaPromise L
        (ActualHeadlineParameters.manuscriptSigma L)
        (ActualHeadlineParameters.manuscriptGamma L) hσ hγ0 hγ1)
      (manuscriptBruteEnc L h) :=
  manuscriptBruteEnc_mapReducesVia h hσ hγ0 hγ1

example {L : Nat} (hL : 0 < L) (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L) :
    (ActualThreeSatToCmmsa.noInstance L
      (ActualHeadlineParameters.manuscriptSigma L) hL).data.budget <
      1 / (ActualHeadlineParameters.manuscriptSigma L : Rat) :=
  manuscriptNo_budget_lt_inv_sigma hL hσ

#check manuscriptBrute_no_sat_zero
#check manuscriptBrute_vanishing_gap_not_fp_witness
#print axioms manuscriptBrute_no_sat_zero
#print axioms manuscriptBrute_vanishing_gap_not_fp_witness
#check manuscriptBruteEnc_mem_FP_iff_threeSat_in_P
#check manuscriptBruteEnc_mem_FP_iff_P_eq_NP
#check exists_fp_manuscript_map_of_P_eq_NP
#check not_exists_fp_manuscript_map_implies_P_ne_NP
#print axioms manuscriptBruteEnc_mem_FP_iff_threeSat_in_P
#print axioms manuscriptBruteEnc_mem_FP_iff_P_eq_NP
#print axioms exists_fp_manuscript_map_of_P_eq_NP
#print axioms not_exists_fp_manuscript_map_implies_P_ne_NP

example {L : Nat} (h : 256 ≤ ActualHeadlineParameters.mOf L)
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hf : manuscriptBruteEnc L h ∈ Complexity.FP) :
    Complexity.SAT.ThreeSAT.language ∈ Complexity.P :=
  threeSat_in_P_of_manuscriptBrute_mem_FP h hσ hf

example {L : Nat} (h : 256 ≤ ActualHeadlineParameters.mOf L)
    (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
    (hf : manuscriptBruteEnc L h ∈ Complexity.FP) :
    Complexity.SAT.ThreeSAT.language ∈ Complexity.P :=
  manuscriptBrute_collapses h hσ hf

example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∀ (h : 256 ≤ ActualHeadlineParameters.mOf L)
        (hσ : 1 ≤ ActualHeadlineParameters.manuscriptSigma L)
        (hγ0 : 0 < ActualHeadlineParameters.manuscriptGamma L)
        (hγ1 : ActualHeadlineParameters.manuscriptGamma L < 1),
        ActualSatToThreeSatSource.threeSatSource.MapReducesVia
            (ActualCMMSARandomizedReduction.cmmsaPromise L
              (ActualHeadlineParameters.manuscriptSigma L)
              (ActualHeadlineParameters.manuscriptGamma L) hσ hγ0 hγ1)
            (manuscriptBruteEnc L h) ∧
          (manuscriptBruteEnc L h ∈ Complexity.FP →
            Complexity.SAT.ThreeSAT.language ∈ Complexity.P) := by
  obtain ⟨L0, hL0⟩ := manuscriptBrute_interface_eventual
  refine ⟨L0, ?_⟩
  intro L hL h hσ hγ0 hγ1
  obtain ⟨hred, _, hP⟩ := hL0 L hL h hσ hγ0 hγ1
  exact ⟨hred, hP⟩

end PvNP.RealizableHardness.ActualThreeSatManuscriptBruteKillChecks
