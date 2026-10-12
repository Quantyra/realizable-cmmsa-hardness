import PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant

/-! The actual selected-leaf HC46 consumer with the original analytic
contract discharged, rather than retained as a caller hypothesis. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementHC46OriginalApplication
open ActualSelectedComplementAnalyticMoment
open ActualBinaryMatrixHC46OriginalExactInhabitant
open BinaryMatrixFourier ActualFixedFunctionalBinaryMatrixMoment
open ActualComplementCoordinateMassBridge
open MatrixLiftNominalDirectComparison ActualFixedFunctionalStarMoment
set_option autoImplicit false
noncomputable section

theorem selected_leaf_HC46_original {n h r i p : Nat} {eta : Real}
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (2 * h))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (hPR : PseudorandomExact r eta (rankImageBoolean (leafMatchBit T f)))
    (hi : i ≤ r) (hp4 : 4 ≤ p) (hpDyadic : ∃ q : Nat, p = 2 ^ q) :
    lpNorm p (rankProjection i (indicator (rankImageBoolean (leafMatchBit T f)))) ≤
      (2 : Real) ^ (500 * i ^ 2 * p) * eta ^ (((p : Real) - 2) / (p : Real)) := by
  exact selected_leaf_HC46_of_exact_PR T f hPR hi hp4 hpDyadic original_HC46_exact

theorem selected_leaf_failed_zoom_HC46_original {n h r i p : Nat}
    (hrd : r < 2 * h)
    (T : ActualSourceStarLaw.LeafTable (V := Fin n → ZMod 2) (2 * h))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2))
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat) (Q : GrassmannCounting.Grass (Fin n → ZMod 2) q)
      (P : ActualMaximalPairLadder.DecodedPair Q (2 * h)),
      q + ActualMaximalPairLadder.codim P.W = r →
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
          ActualMaximalPairLadder.agreement (fun L => T L) Q P ≤ e)
    (hi : i ≤ r) (hp4 : 4 ≤ p) (hpDyadic : ∃ q : Nat, p = 2 ^ q) :
    lpNorm p (rankProjection i (indicator (rankImageBoolean (leafMatchBit T f)))) ≤
      (2 : Real) ^ (500 * i ^ 2 * p) *
        (2 * (e : Real)) ^ (((p : Real) - 2) / (p : Real)) := by
  exact selected_leaf_HC46_original T f
    (selected_leaf_failed_zoom_PR hrd T f e he hfail) hi hp4 hpDyadic


/-! Same material consumer with only the universal HC46 premise discharged.
Spectral47, selector, failed-zoom and positive-parameter premises remain explicit.
This candidate has not been compiled or independently accepted. -/
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.MatrixGrassmannIdentity
open PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.SamplerParameters
attribute [local instance] Classical.propDecidable

theorem selected_actual_material_moment_bound_original
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
      (fun j => max (analyticSourceHeightFloor base sourceHeightCutoff j) (j + 2)) L =
        (m : WithBot Nat))
    (hA : 1 ≤ samplerA) (r : Nat) (hrd : r <
      ActualStarFixedRhoDimensionGuard.leafT m
        (ActualCmmsaParameterReconciliation.hBlock L m) +
      ActualStarFixedRhoDimensionGuard.leafK m
        (ActualCmmsaParameterReconciliation.hBlock L m))
    (e : Rat) (he : 0 ≤ e)
    (hfail : ∀ (q : Nat)
      (Q : Grass (CoordAmbient (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m))) q)
      (P : ActualMaximalPairLadder.DecodedPair Q
        (ActualStarFixedRhoDimensionGuard.leafT m
          (ActualCmmsaParameterReconciliation.hBlock L m) +
         ActualStarFixedRhoDimensionGuard.leafK m
          (ActualCmmsaParameterReconciliation.hBlock L m))),
      q + ActualMaximalPairLadder.codim P.W = r →
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
          ActualMaximalPairLadder.agreement
            (fun X => selectedCoordinateLeafTable I copies U A T X) Q P ≤ e)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
    (a : Real) (ha : 0 < a) :
    let h := ActualCmmsaParameterReconciliation.hBlock L m
    let J := SamplerParameters.blocks samplerA h
    let c := ActualStarFixedRhoDimensionGuard.leafT m h
    let s := ActualStarFixedRhoDimensionGuard.leafK m h
    let n := 2 * J
    let Cc := selectedCoordinateCenterTable I copies U A C
    let Tc : ActualSourceStarLaw.LeafTable
        (V := Fin n → ZMod 2) (c + s) :=
      selectedCoordinateLeafTable I copies U A T
    let fc := coordinateFunctional I copies U A f
    ∃ k q : Nat, k = 2 ^ q ∧ 4 * m ≤ k ∧ k < 8 * m ∧
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) ≤
        2 * selected_actual_analytic_rhs (n := n) (c := c) (s := s) (m := m)
          Cc Tc fc r k (2 * (e : Real)) a ∧
      (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C) f : Real) =
        (∑ R : Grass (CoordAmbient J) c,
          if centerMatchBit Cc fc R then (1 : Real) else 0) /
            (Fintype.card (Grass (CoordAmbient J) c) : Real) := by
  exact selected_actual_material_moment_bound I copies U A C T f
    base sourceHeightCutoff hsel hA r hrd e he hfail
    original_HC46_exact hSpectral a ha

end
end PvNP.RealizableHardness.ActualSelectedComplementHC46OriginalApplication
