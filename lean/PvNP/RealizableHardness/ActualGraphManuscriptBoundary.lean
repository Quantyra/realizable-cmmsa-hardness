import PvNP.RealizableHardness.ActualBudgetOneObstruction
import PvNP.RealizableHardness.ActualThreeSatGraphYes
import PvNP.RealizableHardness.ActualThreeSatUniformEncKill
import Complexitylib.SAT.ThreeSAT

/-!
Constraint-graph one-hot encoding at manuscript `σ_L` and `γ_L`.

`threeSatToGraphBits` reads a 3CNF. On a satisfiable formula the honest
one-hot of `vertexLabel` is a `Yes 0` witness, so the bits lie in
`yesInstances`. On the fixed unsatisfiable `falseFormula`, symbols `0` and
`1` at every vertex satisfy each `dummyAnd` branch. That lighting costs
`1/4` and the budget is `1/8`, so once `manuscriptSigma ≥ 2` the bits are
not a `No` instance.

This is not the clause-query star family. It does not meet the manuscript
no-bound, and it does not build a `SeededMap` or discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualGraphManuscriptBoundary

open ActualBudgetOneObstruction
open ActualCertifiedManuscriptParameters
open ActualCMMSARandomizedReduction
open ActualHeadlineParameters
open ActualThreeSatGraphData
open ActualThreeSatGraphYes
open ActualThreeSatUniformEncKill
open CMMSACodec hiding Tree
open CMMSAEncoding
open Complexity
open Complexity.SAT
open Complexity.SAT.ThreeSAT

set_option autoImplicit false

theorem falseFormula_len : 0 < falseFormula.length := by
  decide

theorem graph_bits_manuscript_yes_satUnit {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hγ0 : 0 < manuscriptGamma L)
    (hγ1 : manuscriptGamma L < 1) :
    threeSatToGraphBits h satUnit satUnit_is3 satUnit_len ∈
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).yesInstances :=
  threeSatToGraphBits_yes_of_sat h hσ hγ0 hγ1 satUnit satUnit_is3 satUnit_len
    [true] satUnit_sat

theorem graph_bits_manuscript_false_not_no {L : Nat} (h : 256 ≤ mOf L)
    (hσ : 1 ≤ manuscriptSigma L) (hσ2 : 2 ≤ manuscriptSigma L)
    (hγ0 : 0 < manuscriptGamma L) (hγ1 : manuscriptGamma L < 1) :
    threeSatToGraphBits h falseFormula falseFormula_is3CNF falseFormula_len ∉
      (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).noInstances := by
  intro hmem
  have hv := graphData_valid falseFormula falseFormula_len (one_twenty_eight_le_L h)
  obtain ⟨i, hi, hN⟩ := hmem
  have hbits :
      threeSatToGraphBits h falseFormula falseFormula_is3CNF falseFormula_len =
        encodeData (graphData falseFormula falseFormula_len) hv := by
    simp [threeSatToGraphBits, paramGraphData]
  have hdec :
      decode L (encodeData (graphData falseFormula falseFormula_len) hv) =
        some (ofData (graphData falseFormula falseFormula_len) hv) := by
    simp [encodeData, decode_encode]
  rw [hbits] at hi
  have hi' : i = ofData (graphData falseFormula falseFormula_len) hv :=
    Option.some.inj (hi.symm.trans hdec)
  subst hi'
  exact graphData_not_no falseFormula falseFormula_len hv hσ2 hγ1 hN

/-- For every large `L`, the sat unit is a manuscript yes-instance and the
fixed unsatisfiable formula is not a manuscript no-instance. -/
theorem graph_manuscript_yes_sat_not_no_unsat :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hm : 256 ≤ mOf L) (hσ : 1 ≤ manuscriptSigma L) (_hσ2 : 2 ≤ manuscriptSigma L)
        (hγ0 : 0 < manuscriptGamma L) (hγ1 : manuscriptGamma L < 1),
        threeSatToGraphBits hm satUnit satUnit_is3 satUnit_len ∈
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).yesInstances ∧
          threeSatToGraphBits hm falseFormula falseFormula_is3CNF falseFormula_len ∉
            (cmmsaPromise L (manuscriptSigma L) (manuscriptGamma L) hσ hγ0 hγ1).noInstances := by
  obtain ⟨Lm, hLm⟩ := mOf_unbounded 256
  obtain ⟨Ls, hLs⟩ := manuscriptSigma_ge_two_eventual
  obtain ⟨Lg, hLg⟩ := certifiedGamma_pos_lt_one_eventual
  refine ⟨max Lm (max Ls Lg), ?_⟩
  intro L hL
  have hLm' : Lm ≤ L := le_trans (Nat.le_max_left _ _) hL
  have hLs' : Ls ≤ L :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hL
  have hLg' : Lg ≤ L :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hL
  have hm : 256 ≤ mOf L := hLm L hLm'
  have hσ2 : 2 ≤ manuscriptSigma L := hLs L hLs'
  have hσ : 1 ≤ manuscriptSigma L := le_trans (by decide) hσ2
  have hγ := hLg L hLg'
  have hγ0 : 0 < manuscriptGamma L := by simpa [manuscriptGamma] using hγ.1
  have hγ1 : manuscriptGamma L < 1 := by simpa [manuscriptGamma] using hγ.2
  exact ⟨hm, hσ, hσ2, hγ0, hγ1,
    graph_bits_manuscript_yes_satUnit hm hσ hγ0 hγ1,
    graph_bits_manuscript_false_not_no hm hσ hσ2 hγ0 hγ1⟩

end PvNP.RealizableHardness.ActualGraphManuscriptBoundary
