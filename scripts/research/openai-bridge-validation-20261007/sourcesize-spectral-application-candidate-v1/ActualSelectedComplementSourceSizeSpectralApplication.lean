import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeOriginalApplication
import PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment
import PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant
import PvNP.RealizableHardness.SourceSizeContractBridge

/-! Uncompiled successor candidate: actual SourceSize material and caller-chosen
dyadic consumers discharge Spectral47 through the native contract bridge.
Original HC46 remains supplied by the original consumer. All other premises
and conclusions are retained exactly. No source/runtime or manuscript GO. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementSourceSizeSpectralApplication
open PvNP.RealizableHardness.ActualAppendFourierCrossLevelOrthogonality
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFixedFunctionalBinaryMatrixMoment
open PvNP.RealizableHardness.ActualFixedFunctionalStarMoment
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.MatrixGrassmannIdentity
open PvNP.RealizableHardness.MatrixLiftNominalDirectComparison
open PvNP.RealizableHardness.SamplerParameters
open PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

theorem selected_actual_material_moment_bound_original_spectral_discharged
    {N rows m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
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
  exact PvNP.RealizableHardness.ActualSelectedComplementSourceSizeOriginalApplication.selected_actual_material_moment_bound_original I copies U A C T f
    base sourceHeightCutoff hsel hA r hrd e he hfail
    ((PvNP.RealizableHardness.SourceSizeContractBridge.spectral47_contract_iff
      sourceHeightCutoff).mp
      (PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.
        spectral47_exact_contract_inhabitant sourceHeightCutoff))
    a ha

theorem selected_actual_material_moment_bound_original_at_dyadic_exponent_spectral_discharged
    {N rows m L samplerA k : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
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
    (a : Real) (ha : 0 < a)
    (hkDyadic : ∃ q : Nat, k = 2 ^ q) (hkm : 4 * m ≤ k) :
    let h := ActualCmmsaParameterReconciliation.hBlock L m
    let J := SamplerParameters.blocks samplerA h
    let c := ActualStarFixedRhoDimensionGuard.leafT m h
    let s := ActualStarFixedRhoDimensionGuard.leafK m h
    let n := 2 * J
    let Cc := selectedCoordinateCenterTable I copies U A C
    let Tc : ActualSourceStarLaw.LeafTable
        (V := Fin n → ZMod 2) (c + s) :=
      selectedCoordinateLeafTable I copies U A T
    let fc := coordinateFunctional I copies U A f;
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
  exact PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment.selected_actual_material_moment_bound_original_at_dyadic_exponent I copies U A C T f
    base sourceHeightCutoff hsel hA r hrd e he hfail
    ((PvNP.RealizableHardness.SourceSizeContractBridge.spectral47_contract_iff
      sourceHeightCutoff).mp
      (PvNP.RealizableHardness.ActualFiniteAppendSpectral47ExactInhabitant.
        spectral47_exact_contract_inhabitant sourceHeightCutoff))
    a ha hkDyadic hkm

end
end PvNP.RealizableHardness.ActualSelectedComplementSourceSizeSpectralApplication
