import PvNP.RealizableHardness.ActualEdgeBlockStar
import PvNP.RealizableHardness.ActualFpMapInterface

/-!
The grouped Dinur edge-block mass is not a uniform one-hot manuscript `No`.

`edgeBlockAcceptanceMass_le_modified_pcp` bounds every assignment of an
unsatisfiable 3CNF by `1 / modifiedPcpDenom`. `dinur_alphabet_one_hot_eventually_not_no`
says a uniform one-hot budget on `DinurAlpha` is eventually not manuscript
`No`, because the all-true assignment enters the `σ` ball. The two facts
hold together, so the mass bound is not that `No` instance.

This file does not build a `SeededMap` and does not discharge `hSrcCmmsa`.
-/
namespace PvNP.RealizableHardness.ActualEdgeBlockOneHot

open ActualEdgeBlockStar
open ActualDinurShrinkingCeiling
open ActualModifiedPcpCeiling
open ActualFpMapInterface
open ActualCertifiedManuscriptParameters
open ActualHeadlineParameters
open CMMSACodec
open Complexity
open Complexity.SAT
open Dinur

set_option autoImplicit false

noncomputable section

theorem edge_block_mass_and_dinur_one_hot_not_no :
    ∃ L0, ∀ L, L0 ≤ L →
      (∀ (φ : CNF), φ.Is3CNF → ¬ φ.Satisfiable →
        ∀ a : (manuscriptGap φ).Assignment,
          edgeBlockAcceptanceMass φ L a ≤
            ((modifiedPcpDenom L (certifiedM L) : Rat))⁻¹) ∧
      (∀ i : Instance L,
        (1 : Rat) / (Fintype.card DinurAlpha : Rat) ≤ i.data.budget →
        i.data.cost (fun _ => true) = 1 →
        ¬ No (manuscriptSigma L) (manuscriptGamma L) i) := by
  obtain ⟨L0, hL0⟩ := dinur_alphabet_one_hot_eventually_not_no
  refine ⟨L0, ?_⟩
  intro L hL
  refine ⟨?_, hL0 L hL⟩
  intro φ h3 hunsat a
  exact edgeBlockAcceptanceMass_le_modified_pcp h3 hunsat L a

end

end PvNP.RealizableHardness.ActualEdgeBlockOneHot
