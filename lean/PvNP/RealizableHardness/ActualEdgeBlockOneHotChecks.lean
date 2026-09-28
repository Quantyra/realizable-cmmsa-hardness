import PvNP.RealizableHardness.ActualEdgeBlockOneHot

/-!
Checks for the edge-block mass together with the Dinur one-hot `No`
obstruction. The example calls the shipped theorem. Axioms print after.
This file does not inhabit `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualEdgeBlockOneHotChecks

open ActualEdgeBlockOneHot
open ActualEdgeBlockStar
open ActualDinurShrinkingCeiling
open ActualModifiedPcpCeiling
open ActualFpMapInterface
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open CMMSACodec
open Complexity
open Complexity.SAT

#check edge_block_mass_and_dinur_one_hot_not_no

example :
    ∃ L0, ∀ L, L0 ≤ L →
      (∀ (φ : CNF), φ.Is3CNF → ¬ φ.Satisfiable →
        ∀ a : (manuscriptGap φ).Assignment,
          edgeBlockAcceptanceMass φ L a ≤
            ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹) ∧
      (∀ i : Instance L,
        (1 : Rat) / (Fintype.card DinurAlpha : Rat) ≤ i.data.budget →
        i.data.cost (fun _ => true) = 1 →
        ¬ No (manuscriptSigma L) (manuscriptGamma L) i) :=
  edge_block_mass_and_dinur_one_hot_not_no

#print axioms edge_block_mass_and_dinur_one_hot_not_no

end PvNP.RealizableHardness.ActualEdgeBlockOneHotChecks
