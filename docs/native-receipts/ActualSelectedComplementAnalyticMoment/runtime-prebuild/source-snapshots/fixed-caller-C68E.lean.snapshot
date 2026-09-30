import PvNP.RealizableHardness.ActualOriginalFailureAnalyticCaller
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
import PvNP.RealizableHardness.ActualSelectedComplementAppendMoment

/-! Fixed-moment original-failure caller. The moment exponent and Holder scale
are explicit powers of the accepted numerical source bound. This module does
not import the mutable Margin layer and keeps HC46/Spectral47 conditional. -/
namespace PvNP.RealizableHardness.ActualOriginalFailureFixedMomentCaller

open PvNP.RealizableHardness
open PvNP.RealizableHardness.GrassmannCounting
open PvNP.RealizableHardness.ActualMaximalPairLadder
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
open PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
open PvNP.RealizableHardness.ActualSelectedSpectralParameters
open PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
open PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
open PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
open PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

def fixedMomentK (m : Nat) : Nat :=
  2 ^ ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound m

def fixedMomentP (m : Nat) : Nat :=
  2 ^ (m * fixedMomentK m)

theorem fixed_moment_scale_facts {m : Nat} (hm : 256 <= m) :
    (exists qK : Nat, fixedMomentK m = 2 ^ qK) /\
    ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound m <= fixedMomentK m /\
    (exists qP : Nat, fixedMomentP m = 2 ^ qP) /\
    m * fixedMomentK m <= fixedMomentP m /\
    8 * m < fixedMomentP m := by
  let B := ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound m
  have hm1 : 1 <= m := by omega
  have hm3 : 1 <= m + 3 := by omega
  have hKdef : fixedMomentK m = 2 ^ B := by rfl
  have hPdef : fixedMomentP m = 2 ^ (m * fixedMomentK m) := by rfl
  have hKlarge : B <= fixedMomentK m := by
    rw [hKdef]
    exact (Nat.lt_two_pow_self (n := B)).le
  have hKgt8 : 8 < fixedMomentK m := by
    have hA : 16000 <= 16000 * m := Nat.mul_le_mul_left 16000 hm1
    have hB : 16000 * m <= 16000 * m * (m + 3) := by
      simpa using Nat.mul_le_mul_left (16000 * m) hm3
    have hsmall : 8 < B := by
      dsimp [B, ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound]
      nlinarith
    exact hsmall.trans_le hKlarge
  have hPlarge : m * fixedMomentK m <= fixedMomentP m := by
    rw [hPdef]
    exact (Nat.lt_two_pow_self (n := m * fixedMomentK m)).le
  have h8 : 8 * m < m * fixedMomentK m := by nlinarith [hKgt8]
  refine ⟨?_, hKlarge, ?_, hPlarge, ?_⟩
  · exact ⟨B, hKdef⟩
  · exact ⟨m * fixedMomentK m, hPdef⟩
  · exact h8.trans_le hPlarge

theorem selected_actual_fixed_moment_bound_from_source_failure
    {N m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N m)
    (copies : Nat)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies
      (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m)))
    (A : ActualTaggedComplementIncidence.SideComplement I copies U)
    (C : ActualTaggedFixedTableAcceptance.TaggedCenterTable I copies)
    (T : ActualTaggedFixedTableAcceptance.TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (base : Nat -> Nat) (sourceHeightCutoff : Real -> Nat)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max (ActualSelectedSpectralParameters.analyticSourceHeightFloor
        base sourceHeightCutoff j) (j + 2)) L = (m : WithBot Nat))
    (hA : 1 <= samplerA) (r : Nat)
    (hrd : r < ActualStarFixedRhoDimensionGuard.leafT m
        (ActualCmmsaParameterReconciliation.hBlock L m) +
      ActualStarFixedRhoDimensionGuard.leafK m
        (ActualCmmsaParameterReconciliation.hBlock L m))
    (e : Rat) (he : 0 <= e)
    (hfailSource : forall (q : Nat)
      (Q : Grass A.1 q)
      (P : DecodedPair Q
        (ActualStarFixedRhoDimensionGuard.leafT m
            (ActualCmmsaParameterReconciliation.hBlock L m) +
          ActualStarFixedRhoDimensionGuard.leafK m
            (ActualCmmsaParameterReconciliation.hBlock L m))),
      q + codim P.W = r ->
        Fintype.card (Zoom Q P) != 0 ->
          agreement
            (ActualTaggedComplementStarDensityBridge.transportedLeafTable
              I copies U A T) Q P <= e)
    (hHC : ActualSelectedComplementAnalyticMoment.HC46ExactContract)
    (hSpectral : ActualSelectedComplementAnalyticMoment.Spectral47ExactContract
      sourceHeightCutoff)
    (a : Real) (ha : 0 < a) :
    let h := ActualCmmsaParameterReconciliation.hBlock L m
    let J := SamplerParameters.blocks samplerA h
    let c := ActualStarFixedRhoDimensionGuard.leafT m h
    let s := ActualStarFixedRhoDimensionGuard.leafK m h
    let n := 2 * J
    let K := fixedMomentK m
    let P := fixedMomentP m
    let Cc := ActualComplementCoordinateMassBridge.selectedCoordinateCenterTable I copies U A C
    let Tc : ActualSourceStarLaw.LeafTable (V := Fin n -> ZMod 2) (c + s) :=
      ActualComplementCoordinateMassBridge.selectedCoordinateLeafTable I copies U A T
    let fc := ActualComplementCoordinateMassBridge.coordinateFunctional I copies U A f
    ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound m <= K /\
    K = 2 ^ ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound m /\
    P = 2 ^ (m * K) /\
    m * K <= P /\
    8 * m < P /\
    0 < ActualSelectedComplementAnalyticNumerics.acceptedInverseDecayCoefficient m P /\
    (ActualOrdinaryStarWeightedSelection.matchingStarMass
      (V := A.1) (m := m) (Nat.le_add_right c s)
      (ActualSelectedComplementAnalyticMoment.selected_actual_source_dimension_bound
        I copies U A base sourceHeightCutoff hsel hA)
      (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
      (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) <=
      2 * ActualSelectedComplementAnalyticMoment.selected_actual_analytic_rhs
        (n := n) (c := c) (s := s) (m := m) Cc Tc fc r P (2 * (e : Real)) a := by
  intro h J c s n K P Cc Tc fc
  have hparams := ActualSelectedSpectralParameters.selected_spectral_parameters
    base sourceHeightCutoff hsel
  rcases hparams with
    ⟨hm256, hh, hdiv, hhpos, hspos, hsplit, hrhoPos, hrho,
      hcReal, hsReal, hbaseFloor, hcutFloor⟩
  have hm : 0 < m := by omega
  rcases fixed_moment_scale_facts hm256 with
    ⟨hKpow, hKlarge, hPpow, hPlarge, h8m⟩
  have hdim : c + s <= n := by
    have hle : h <= h ^ 2 := by
      simpa [pow_two] using Nat.le_mul_of_pos_left h hhpos
    have hJ : h ^ 2 < J := by
      dsimp [J, h]
      simpa only [one_mul] using
        ((Nat.mul_le_mul_right
          ((ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) hA).trans_lt
          (SamplerParameters.numerator_lt_blocks samplerA
            (ActualCmmsaParameterReconciliation.hBlock L m)))
    have hleJ : h <= J := hle.trans_lt hJ
    calc
      c + s = 2 * h := hsplit
      _ <= 2 * J := Nat.mul_le_mul_left 2 hleJ
  have hfailCoord :=
    ActualOriginalFailureAnalyticCaller.source_failed_zoom_to_selected_coordinate
      I U A T e he hfailSource
  have hfail' : forall (q : Nat)
      (Q : Grass (Fin n -> ZMod 2) q)
      (Qpair : ActualMaximalPairLadder.DecodedPair Q (c + s)),
      q + ActualMaximalPairLadder.codim Qpair.W = r ->
        Fintype.card (ActualMaximalPairLadder.Zoom Q Qpair) != 0 ->
          ActualMaximalPairLadder.agreement (fun X => Tc X) Q Qpair <= e := by
    simpa [ActualComplementCoordinateMassBridge.CoordAmbient,
      ActualLeafLabelRankImageAlignment.Ambient, n, J, c, s, Tc] using hfailCoord
  have hPR :=
    ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
      (r := r) (d := c + s) hrd Tc fc e he hfail'
  have hKfour : 4 * m <= K := by
    have hbase : 4 * m <= ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound m := by
      dsimp [ActualSelectedComplementAnalyticNumerics.sourceHolderLowerBound]
      have hm1 : 1 <= m := by omega
      nlinarith
    exact hbase.trans hKlarge
  have hPfour : 4 * m <= P := by omega
  have hMoment :=
    ActualSelectedComplementAnalyticNumerics.selected_actual_HC_spectral_moment_bound_large_dyadic
      (n := n) (c := c) (s := s) (m := m) (k := P)
      sourceHeightCutoff (C := Cc) (T := Tc) (f := fc) (a := a) ha hm hPfour
      hsplit hrhoPos hcReal hsReal hcutFloor hPR hPpow hHC hSpectral hdim
  have hMass :=
    ActualSelectedComplementAppendMoment.selected_actual_append_moment
      I copies U A C T f
      (ActualSelectedSpectralParameters.analyticSourceHeightFloor
        base sourceHeightCutoff) hsel hA
  have hMassMoment :
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (ActualSelectedComplementAnalyticMoment.selected_actual_source_dimension_bound
          I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) <=
        2 * ActualSelectedComplementAnalyticMoment.selectedActualMoment
          (m := m)
          (ActualSelectedComplementAnalyticMoment.selectedG Cc fc)
          (ActualSelectedComplementAnalyticMoment.selectedF Tc fc) := by
    simpa [ActualFixedFunctionalAppendOperator.actualAppendRankImageMoment,
      ActualSelectedComplementAnalyticMoment.selectedActualMoment,
      ActualSelectedComplementAnalyticMoment.selectedG,
      ActualSelectedComplementAnalyticMoment.selectedF,
      ActualFixedFunctionalAppendOperator.CoordinateAmbient,
      ActualComplementCoordinateMassBridge.CoordAmbient] using hMass
  have hMomentRhs :
      ActualSelectedComplementAnalyticMoment.selectedActualMoment
          (m := m)
          (ActualSelectedComplementAnalyticMoment.selectedG Cc fc)
          (ActualSelectedComplementAnalyticMoment.selectedF Tc fc) <=
        ActualSelectedComplementAnalyticMoment.selected_actual_analytic_rhs
          (n := n) (c := c) (s := s) (m := m)
          Cc Tc fc r P (2 * (e : Real)) a := by
    simpa [ActualSelectedComplementAnalyticMoment.selected_actual_analytic_rhs] using hMoment
  have hfinal := hMassMoment.trans
    (mul_le_mul_of_nonneg_left hMomentRhs (by norm_num : (0 : Real) <= 2))
  have hdecaySource :=
    ActualSelectedComplementAnalyticNumerics.manuscript_large_holder_decay_positive
      hm256 hKlarge
  have hdecayCompare :=
    ActualSelectedComplementAnalyticNumerics.selected_holder_decay_dominates_source
      hm256 hKlarge hPlarge
  have hdecay :
      0 < ActualSelectedComplementAnalyticNumerics.acceptedInverseDecayCoefficient m P :=
    lt_of_lt_of_le hdecaySource hdecayCompare
  exact ⟨hKlarge, rfl, rfl, hPlarge, h8m, hdecay, hfinal⟩

end
end PvNP.RealizableHardness.ActualOriginalFailureFixedMomentCaller