import PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualCmmsaParameterReconciliation
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment
import PvNP.RealizableHardness.ActualOriginalFailureAnalyticCaller
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticNumerics
import PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
import PvNP.RealizableHardness.SamplerParameters

/-! Row-generic fixed-moment source-failure consumer. Its analytic moment
parameter is independent of the row-index carried by the occurrence instance.
The local append-moment proof is the same source proof with that index split. -/
namespace PvNP.RealizableHardness.ActualOriginalFailureRowGenericFixedMomentCaller

open PvNP.RealizableHardness
open ActualOccurrenceAllocation
open ActualTaggedComplementIncidence
open ActualTaggedConcreteStarLaw
open ActualTaggedFixedTableAcceptance
open ActualOrdinaryStarWeightedSelection
open ActualFixedFunctionalStarMoment
open ActualTaggedComplementStarDensityBridge
open ActualFixedFunctionalBinaryMatrixMoment
open ActualComplementCoordinateMassBridge
open ActualFixedFunctionalAppendOperator
open ActualStarFixedRhoDimensionGuard
open ActualCmmsaAdmissibilitySelector
open ActualCmmsaParameterReconciliation
open ActualSelectedSpectralParameters
open ActualSelectedComplementAnalyticMoment
open ActualSelectedComplementAnalyticNumerics
open ActualLeafLabelRankImageAlignment
open ActualMaximalPairLadder
open GrassmannCounting
open SamplerParameters

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
private theorem selected_rankloss_exponent
    {m h J c s A : Nat} (hm : 256 ≤ m) (hh : m + 2 ≤ h)
    (hA : 1 ≤ A) (hJ : J = blocks A h)
    (hc : c = leafT m h) (hs : s = leafK m h) :
    c + s = 2 * h ∧ c + m * s + 2 * h ≤ 2 * J := by
  subst hJ
  subst hc
  subst hs
  have hmpos : 0 < m := by omega
  have htle : leafT m h ≤ 2 * h := by
    dsimp [leafT]
    exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  have hsle : leafK m h ≤ 2 * h := by
    dsimp [leafK]
    exact Nat.sub_le _ _
  have hsum : leafT m h + leafK m h = 2 * h := by
    change leafT m h + (2 * h - leafT m h) = 2 * h
    exact Nat.add_sub_of_le htle
  have hpoly : leafT m h + m * leafK m h + 2 * h ≤ 2 * h ^ 2 := by
    have hmul : m + 1 ≤ h - 1 := by omega
    calc
      leafT m h + m * leafK m h + 2 * h ≤ 2 * h + m * (2 * h) + 2 * h := by
        exact Nat.add_le_add (Nat.add_le_add htle (Nat.mul_le_mul_left m hsle)) le_rfl
      _ = 2 * h * (m + 1) + 2 * h := by ring
      _ ≤ 2 * h * (h - 1) + 2 * h := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left (2 * h) hmul) _
      _ = 2 * h ^ 2 := by
        have hminus : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
        calc
          2 * h * (h - 1) + 2 * h = 2 * h * ((h - 1) + 1) := by ring
          _ = 2 * h * h := by rw [hminus]
          _ = 2 * h ^ 2 := by ring
  have hpow : h ^ 2 < blocks A h := by
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ ≤ A * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < blocks A h := by
        simpa only [one_mul] using numerator_lt_blocks A h
  constructor
  · exact hsum
  · have hsmall : leafT m h + m * leafK m h + 2 * h ≤ 2 * h ^ 2 := hpoly
    have hb : 2 * h ^ 2 ≤ 2 * blocks A h := Nat.mul_le_mul_left 2 hpow.le
    simpa using hsmall.trans hb

private theorem rankloss_from_exponent
    {h J c s m : Nat} (hh : 0 < h)
    (hsum : c + s = 2 * h)
    (hbudget : c + m * s + 2 * h ≤ 2 * J) :
    ((c + m * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
        (2 : Real) ^ (2 * J) ≤ 1 / 2 := by
  let N0 := c + m * s
  have hNpos : 0 < 2 * h := by omega
  have hnumerator : (N0 : Real) ≤ (2 : Real) ^ N0 := by
    have hn : N0 < 2 ^ N0 := Nat.lt_two_pow_self
    exact_mod_cast hn.le
  have hexp : N0 + (2 * h - 1) ≤ 2 * J - 1 := by omega
  have hp : (2 : Real) ^ (N0 + (2 * h - 1)) ≤
      (2 : Real) ^ (2 * J - 1) := by
    exact pow_le_pow_right₀ (by norm_num) hexp
  have hprod : (N0 : Real) * (2 : Real) ^ (2 * h - 1) ≤
      (2 : Real) ^ (2 * J - 1) := by
    calc
      (N0 : Real) * (2 : Real) ^ (2 * h - 1) ≤
          (2 : Real) ^ N0 * (2 : Real) ^ (2 * h - 1) :=
        mul_le_mul_of_nonneg_right hnumerator (by positivity)
      _ = (2 : Real) ^ (N0 + (2 * h - 1)) := by rw [← pow_add]
      _ ≤ (2 : Real) ^ (2 * J - 1) := hp
  rw [hsum]
  exact (div_le_iff₀ (by positivity : (0 : Real) < (2 : Real) ^ (2 * J))).2
    (calc
      (N0 : Real) * (2 : Real) ^ (2 * h - 1) ≤ (2 : Real) ^ (2 * J - 1) := hprod
      _ = (1 / 2 : Real) * (2 : Real) ^ (2 * J) := by
        have he : 2 * J - 1 + 1 = 2 * J := by omega
        have hden : (2 : Real) ^ (2 * J) =
            (2 : Real) ^ (2 * J - 1) * 2 := by
          calc
            (2 : Real) ^ (2 * J) = (2 : Real) ^ ((2 * J - 1) + 1) :=
              congrArg (fun e : Nat => (2 : Real) ^ e) he.symm
            _ = (2 : Real) ^ (2 * J - 1) * 2 := by rw [pow_succ]
        rw [hden]
        ring)

theorem selected_actual_append_moment_row_generic
    {N rows m L samplerA : Nat} (I : Instance N rows) (copies : Nat)
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U)
    (C : TaggedCenterTable I copies) (T : TaggedLeafTable I copies)
    (f : Module.Dual (ZMod 2) A.1)
    (sourceHMin : Nat → Nat)
    (hsel : selector (fun n => max (sourceHMin n) (n + 2)) L = (m : WithBot Nat))
    (hA : 1 ≤ samplerA) :
    let h := hBlock L m
    let J := blocks samplerA h
    let c := leafT m h
    let s := leafK m h
    let k := m
    let n := 2 * J
    (matchingStarMass (V := A.1) (m := k) (Nat.le_add_right c s)
      (by
        have hs := selector_spec hsel
        rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
        have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
        have hp : h ^ 2 < J := by
          dsimp [h, J]
          simpa only [one_mul] using
            ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
              (numerator_lt_blocks samplerA (hBlock L m)))
        have hpos : 0 < h := by omega
        have hle : h ≤ h ^ 2 := by
          simpa [pow_two] using (Nat.le_mul_of_pos_left h hpos)
        rw [sideComplement_finrank I copies U A]
        have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
        have hsum := hd.1
        have hbudget := hd.2
        change c + s ≤ 2 * J
        omega)
      (transportedCenterTable I copies U A C)
      (transportedLeafTable I copies U A T) f : Real) ≤
        2 * actualAppendRankImageMoment (n := n) (c := c) (s := s)
          (fun R => centerMatchBit (selectedCoordinateCenterTable I copies U A C)
            (coordinateFunctional I copies U A f) R)
          (fun W => leafMatchBit (selectedCoordinateLeafTable I copies U A T)
            (coordinateFunctional I copies U A f) W) k := by
  intro h J c s k n
  have hs := selector_spec hsel
  rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
  have hh : m + 2 ≤ h := (Nat.le_max_right _ _).trans hcut
  have hbudgetData := selected_rankloss_exponent hm hh hA rfl rfl rfl
  have hp : h ^ 2 < J := by
    dsimp [h, J]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
        (numerator_lt_blocks samplerA (hBlock L m)))
  have hpos : 0 < h := by omega
  have hle : h ≤ h ^ 2 := by
    simpa [pow_two] using (Nat.le_mul_of_pos_left h hpos)
  have hdim : c + s ≤ Module.finrank (ZMod 2) A.1 := by
    rw [sideComplement_finrank I copies U A]
    have hsum := hbudgetData.1
    have hbudget := hbudgetData.2
    change c + s ≤ 2 * J
    omega
  have hsum : c + s = 2 * h := hbudgetData.1
  have hD : 0 < c + s := by rw [hsum]; omega
  have hbudget : c + m * s + 2 * h ≤ 2 * J := hbudgetData.2
  have hsmall := rankloss_from_exponent hpos
    hbudgetData.1 hbudget
  have hfinrank : Module.finrank (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) = 2 * J := by
    simp [ActualFixedFunctionalAppendOperator.CoordinateAmbient, n]
  have hsmall' : ((c + k * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
      (2 : Real) ^ Module.finrank (ZMod 2)
        (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) ≤ 1 / 2 := by
    rw [hfinrank]
    simpa [c, s, k] using hsmall
  have hbound := matchingStarMass_cast_le_twice_actualAppendRankImageMoment
    (n := n) (c := c) (s := s) (k := k)
    (by
      simp [ActualFixedFunctionalAppendOperator.CoordinateAmbient, n]
      have hd := selected_rankloss_exponent hm hh hA rfl rfl rfl
      have hsum' := hd.1
      have hbudget' := hd.2
      change leafT m h + leafK m h ≤ 2 * J
      omega) hD hsmall'
    (selectedCoordinateCenterTable I copies U A C)
    (selectedCoordinateLeafTable I copies U A T)
    (coordinateFunctional I copies U A f)
  have hcoord := matchingStarMass_actual_coordinate (m := k) I copies U A
    (Nat.le_add_right c s) hdim C T f
  calc
    (matchingStarMass (V := A.1) (m := k) (Nat.le_add_right c s)
      hdim
      (transportedCenterTable I copies U A C)
      (transportedLeafTable I copies U A T) f : Real) =
        (matchingStarMass (V := CoordAmbient J) (m := k)
          (Nat.le_add_right c s)
          (actualCoordinateDimensionBound I copies U A hdim)
          (selectedCoordinateCenterTable I copies U A C)
          (selectedCoordinateLeafTable I copies U A T)
          (coordinateFunctional I copies U A f) : Real) := by
            exact_mod_cast hcoord
    _ ≤ _ := hbound

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

/-- Selector-derived source dimension with independent row and analytic-moment
indices. The proof uses only the selected sampler fiber and its height guards. -/
theorem selected_source_dimension_bound
    {N rows L samplerA m : Nat} (I : Instance N rows) (copies : Nat)
    (U : TaggedGoodU I copies (blocks samplerA (hBlock L m)))
    (A : SideComplement I copies U) (base : Nat -> Nat)
    (sourceHeightCutoff : Real -> Nat)
    (hsel : selector (fun j => max (analyticSourceHeightFloor base sourceHeightCutoff j)
      (j + 2)) L = (m : WithBot Nat))
    (hA : 1 <= samplerA) :
    leafT m (hBlock L m) + leafK m (hBlock L m) <=
      Module.finrank (ZMod 2) A.1 := by
  have hs := selector_spec hsel
  rcases hs.1 with ⟨hm, _, _, _, _, _, _, hcut, _⟩
  let h := hBlock L m
  let J := blocks samplerA h
  have hh : m + 2 <= h := (Nat.le_max_right _ _).trans hcut
  have hp : h ^ 2 < J := by
    dsimp [J, h]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right (hBlock L m ^ 2) hA).trans_lt
        (numerator_lt_blocks samplerA (hBlock L m)))
  have hpos : 0 < h := by omega
  have hle : h <= h ^ 2 := by simpa [pow_two] using Nat.le_mul_of_pos_left h hpos
  have hsplit := leaf_split_total (m := m) (h := h)
  have hsmall : h <= J := by omega
  rw [sideComplement_finrank I copies U A]
  change leafT m h + leafK m h <= 2 * J
  omega
theorem selected_actual_fixed_moment_bound_from_source_failure
    {N rows m L samplerA : Nat} (I : ActualOccurrenceAllocation.Instance N rows)
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
        Fintype.card (Zoom Q P) ≠ 0 ->
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
      (selected_source_dimension_bound
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
    have hleJ : h <= J := (hle.trans_lt hJ).le
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
        Fintype.card (ActualMaximalPairLadder.Zoom Q Qpair) ≠ 0 ->
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
    selected_actual_append_moment_row_generic
      I copies U A C T f
      (ActualSelectedSpectralParameters.analyticSourceHeightFloor
        base sourceHeightCutoff) hsel hA
  have hMassMoment :
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_source_dimension_bound
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

end ActualOriginalFailureRowGenericFixedMomentCaller
