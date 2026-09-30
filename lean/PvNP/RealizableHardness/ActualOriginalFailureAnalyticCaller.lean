import PvNP.RealizableHardness.ActualCoordinateZoomFailureTransport
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics

/-! Original-side failure-premise integration for the actual selected
large-dyadic material caller. This source keeps the actual tagged I/U/A/C/T/f
data and transports only the universal failure inequality through the
coordinate equivalence; HC46 and spectral contracts remain explicit. -/
namespace PvNP.RealizableHardness.ActualOriginalFailureAnalyticCaller

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A failed-zoom bound for the actual transported source leaf table implies
the same bound for its selected coordinate leaf table, at the same Rat
threshold and for every decoded pair. -/
theorem source_failed_zoom_to_selected_coordinate
    {N rows copies J d r : Nat}
    (I : ActualOccurrenceAllocation.Instance N rows)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies J)
    (A : ActualTaggedComplementIncidence.SideComplement I copies U)
    (T : ActualTaggedFixedTableAcceptance.TaggedLeafTable I copies)
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : Grass A.1 q)
      (P : DecodedPair Q d),
      q + codim P.W = r →
        Fintype.card (Zoom Q P) ≠ 0 →
          agreement
            (ActualTaggedComplementStarDensityBridge.transportedLeafTable
              I copies U A T) Q P ≤ e) :
    ∀ (q : Nat) (Q : Grass (ActualComplementCoordinateMassBridge.CoordAmbient J) q)
      (P : DecodedPair Q d),
      q + codim P.W = r →
        Fintype.card (Zoom Q P) ≠ 0 →
          agreement
            (ActualComplementCoordinateMassBridge.selectedCoordinateLeafTable
              I copies U A T) Q P ≤ e := by
  have htransport :=
    ActualCoordinateZoomFailureTransport.coordinate_failure_of_source_failure
      I copies U A
      (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T)
      e he hfail
  simpa [ActualComplementCoordinateMassBridge.selectedCoordinateLeafTable] using
    htransport

/-- Material large-dyadic caller with the original side-complement universal
failed-zoom premise. The selected theorem receives the premise proved above,
so no coordinate failure or additional coherence/PR assumption is required of
the caller. -/
theorem selected_actual_material_moment_bound_large_dyadic_from_source_failure
    {N m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies
      (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m)))
    (A : ActualTaggedComplementIncidence.SideComplement I copies U)
    (C : ActualTaggedFixedTableAcceptance.TaggedCenterTable I copies)
    (T : ActualTaggedFixedTableAcceptance.TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (base : Nat → Nat) (sourceHeightCutoff : Real → Nat)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max (ActualSelectedSpectralParameters.analyticSourceHeightFloor
        base sourceHeightCutoff j) (j + 2)) L = (m : WithBot Nat))
    (hA : 1 ≤ samplerA) (r : Nat)
    (hrd : r < ActualStarFixedRhoDimensionGuard.leafT m
        (ActualCmmsaParameterReconciliation.hBlock L m) +
      ActualStarFixedRhoDimensionGuard.leafK m
        (ActualCmmsaParameterReconciliation.hBlock L m))
    (e : Rat) (he : 0 ≤ e)
    (hfailSource : ∀ (q : Nat)
      (Q : Grass A.1 q)
      (P : DecodedPair Q
        (ActualStarFixedRhoDimensionGuard.leafT m
            (ActualCmmsaParameterReconciliation.hBlock L m) +
          ActualStarFixedRhoDimensionGuard.leafK m
            (ActualCmmsaParameterReconciliation.hBlock L m))),
      q + codim P.W = r →
        Fintype.card (Zoom Q P) ≠ 0 →
          agreement
            (ActualTaggedComplementStarDensityBridge.transportedLeafTable
              I copies U A T) Q P ≤ e)
    (hHC : ActualSelectedComplementAnalyticMoment.HC46ExactContract)
    (hSpectral : ActualSelectedComplementAnalyticMoment.Spectral47ExactContract
      sourceHeightCutoff)
    (a : Real) (ha : 0 < a) :
    ActualSelectedComplementAnalyticNumerics.selected_actual_material_moment_bound_large_dyadic
      I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he
      (source_failed_zoom_to_selected_coordinate I copies U A T e he hfailSource)
      hHC hSpectral a ha := by
  exact ActualSelectedComplementAnalyticNumerics.selected_actual_material_moment_bound_large_dyadic
    I copies U A C T f base sourceHeightCutoff hsel hA r hrd e he
    (source_failed_zoom_to_selected_coordinate I copies U A T e he hfailSource)
    hHC hSpectral a ha

end
end PvNP.RealizableHardness.ActualOriginalFailureAnalyticCaller
