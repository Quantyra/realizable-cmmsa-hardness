import PvNP.RealizableHardness.ActualShiftStarScore

/-!
Checks for the uniform shift-star score. The examples call the shipped
theorems. Axioms print after. This file does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualShiftStarScoreChecks

open ActualShiftStarScore
open ActualCompiledProduct
open ActualFormulaProduct
open ActualModifiedPcpCompiled
open ActualCertifiedManuscriptParameters
open ActualCmmsaParameterReconciliation
open ActualHeadlineParameters
open StarListDecoding
open StarFormulaInterface
open StarCmmsaSemantics

#check honest_accepts
#check shift_score_eq
#check shift_score_eq_rBlock
#check shift_product_lt_gamma_large

example :
    (shiftStar (fun _ : Fin 1 => (1 : ZMod 2))).accepts
      (honestLabel (fun _ : Fin 1 => (1 : ZMod 2))) :=
  honest_accepts _

example (l : Fin 2 → ZMod 2) :
    score uniformEdge shiftEdges l = ((2 : ℝ) ^ 1)⁻¹ :=
  shift_score_eq l

example (l : Fin 2 → ZMod 2) :
    score uniformEdge shiftEdges l < 1 :=
  shift_score_lt_one (by decide) (by decide) l

example (L : Nat) (l : Fin (certifiedM L + 1) → ZMod (RBlock L (certifiedM L))) :
    score uniformEdge (rBlockShiftEdges L) l =
      ((RBlock L (certifiedM L) : ℝ) ^ certifiedM L)⁻¹ :=
  shift_score_eq_rBlock L l

set_option maxHeartbeats 800000 in
example :
    ∃ L0, ∀ L, L0 ≤ L →
      ∃ (hm : 256 ≤ certifiedM L),
        ∀ (Z : (Σ _v : Fin (certifiedM L + 1),
            ZMod (RBlock L (certifiedM L))) → Bool)
          (_hcost : assignmentCost uniformEdge (rBlockShiftEdges L) Z ≤
            (manuscriptSigma L : ℝ) * starBudget uniformEdge (rBlockShiftEdges L)),
          average (fun ι : Fin (q (certifiedM L)) →
              (Fin (certifiedM L) → ZMod (RBlock L (certifiedM L))) =>
            Formula.eval Z
              (andAll (fun j =>
                  compiledFormula (rBlockShiftEdges L)
                    (shiftEdges_compile (m := certifiedM L)
                      (R := RBlock L (certifiedM L))) (ι j))
                (q_pos_of_certifiedM hm))) <
            certifiedGamma L :=
  shift_product_lt_gamma_large

#print axioms honest_accepts
#print axioms shift_score_eq
#print axioms shift_score_eq_rBlock
#print axioms shift_score_lt_one
#print axioms shift_product_lt_gamma_large

end PvNP.RealizableHardness.ActualShiftStarScoreChecks
