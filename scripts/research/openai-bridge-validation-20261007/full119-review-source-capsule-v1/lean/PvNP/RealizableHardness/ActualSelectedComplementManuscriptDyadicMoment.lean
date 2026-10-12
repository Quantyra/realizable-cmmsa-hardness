import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment
import PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant

/-! Caller-chosen dyadic moment exponent, retaining the actual material lane.
The original fixed-window theorem remains unchanged. Uncompiled candidate. -/
namespace PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment
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
open ActualSelectedComplementSourceSizeAnalyticMoment
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

theorem selected_actual_HC_spectral_moment_bound_at_dyadic_exponent
    (sourceHeightCutoff : Real → Nat)
    {n c s h r m k : Nat} {rho eta : Real}
    (C : ActualSourceStarLaw.CenterTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c)
    (T : ActualSourceStarLaw.LeafTable
      (V := ActualFixedFunctionalAppendOperator.CoordinateAmbient n) (c + s))
    (f : Module.Dual (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient n))
    (a : Real) (ha : 0 < a) (hm : 0 < m)
    (hkm : 4 * m ≤ k)
    (hEven : c + s = 2 * h) (hRho : 0 < rho)
    (hc : (c : Real) = 2 * (1 - rho) * h)
    (hs : (s : Real) = 2 * rho * h)
    (hHeight : sourceHeightCutoff rho ≤ h)
    (hPR : PseudorandomExact r eta (selectedF T f))
    (hkDyadic : ∃ q : Nat, k = 2 ^ q)
    (hHC : HC46ExactContract)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
    (hdim : c + s ≤ n) :
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤
      (2 : Real) ^ m *
        ((((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) ^
            (1 - ((k : Real) / (m : Real))⁻¹)) *
          (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ m) +
      (2 : Real) ^ m * a ^ m *
        ((∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
            if centerMatchBit C f R then (1 : Real) else 0) /
              (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)) +
      (1 / a ^ 2) *
        (∑ i ∈ selectedHighFinIndexSet (c + s) r,
          ((2 : Real) ^ (-(i.val : Real) * ((s : Real) - 1)) +
            3 * (2 : Real) ^ ((i.val : Real) - (n : Real))) *
            uniformMean (fun W =>
              (rankProjection i.val (indicator (selectedF T f)) W) ^ 2)) := by
  let p : Real := (k : Real)
  let beta : Real :=
    (∑ R : Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c,
      if centerMatchBit C f R then (1 : Real) else 0) /
      (Fintype.card (Grass (ActualFixedFunctionalAppendOperator.CoordinateAmbient n) c) : Real)
  have hmR : 0 < (m : Real) := by exact_mod_cast hm
  have hkm' : m ≤ k := by omega
  have hp : 1 ≤ p / (m : Real) := by
    dsimp [p]
    exact (le_div_iff₀ hmR).2 (by
      exact_mod_cast (show 1 * m ≤ k by omega))
  have hbetaDom := selected_center_matrix_mean_le_exact_grassmann_beta C f
    (by simpa [ActualFixedFunctionalAppendOperator.CoordinateAmbient] using
      (show c ≤ n by omega))
  have hcenter0 : 0 ≤ uniformMean (indicator (selectedG C f)) :=
    uniformMean_indicator_nonneg (selectedG C f)
  have hbeta0 : 0 ≤ beta := by
    dsimp [beta]
    exact le_trans hcenter0 hbetaDom
  have hlowHC := selected_low_append_HC46_lpNorm_bound
    (b := selectedF T f) (hEven := hEven) hPR
    (by omega) hkDyadic hHC
  have hlowNorm0 : 0 ≤ lpNorm k (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow (selectedF T f) (r := r)) M) := by
    unfold lpNorm
    exact Real.rpow_nonneg (by
      unfold lpMoment uniformMean
      positivity) _
  have hCsum0 : 0 ≤ selectedLowHC46NormBound
      (d := c + s) (r := r) (p := k) eta := le_trans hlowNorm0 hlowHC
  have hlowMoment := lpMoment_le_pow_of_lpNorm_le
    (show 0 < k by omega)
    (fun M : BinaryMatrix n c =>
      appendAverage (selectedLow (selectedF T f) (r := r)) M)
    (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta)
    hCsum0 hlowHC
  have hlowMoment' : uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) ≤
        (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ k := by
    simpa [lpMoment] using hlowMoment
  have hlowMoment0 : 0 ≤ uniformMean (fun M : BinaryMatrix n c =>
      |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) := by
    unfold uniformMean
    positivity
  have hlowWeighted :
      uniformMean (fun M : BinaryMatrix n c =>
        indicator (selectedG C f) M *
          (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
            (p / (m : Real))) ≤
        uniformMean (fun M : BinaryMatrix n c =>
          |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k) := by
    have hpoint (M : BinaryMatrix n c) :
        indicator (selectedG C f) M *
            (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
              (p / (m : Real)) ≤
          |appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ k := by
      by_cases hG : selectedG C f M = true
      · have hpow := real_pow_moment_div_m_eq_pow (m := m) (k := k) hm
          (abs (appendAverage (selectedLow (selectedF T f) (r := r)) M))
          (abs_nonneg _)
        simpa [p, indicator, hG] using hpow.le
      · simp [indicator, hG]
    unfold uniformMean
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset (BinaryMatrix n c))) (fun M _ => hpoint M)
    have hden : 0 < (Fintype.card (BinaryMatrix n c) : Real) := by positivity
    exact div_le_div_of_nonneg_right hsum hden.le
  have hlowWeighted0 : 0 ≤ uniformMean (fun M : BinaryMatrix n c =>
      indicator (selectedG C f) M *
        (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
          (p / (m : Real))) := by
    unfold uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro M hM
      have hpow : 0 ≤
          (|appendAverage (selectedLow (selectedF T f) (r := r)) M| ^ m) ^
            (p / (m : Real)) :=
        Real.rpow_nonneg (pow_nonneg (abs_nonneg _) m) _
      by_cases hG : selectedG C f M = true
      · simp [indicator, hG, hpow]
      · simp [indicator, hG]
    · positivity
  have hq0 : 0 ≤ (p / (m : Real))⁻¹ := by positivity
  have hlowpow := Real.rpow_le_rpow hlowWeighted0 hlowWeighted hq0
  have hkR : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hqInv : (p / (m : Real))⁻¹ = (m : Real) / (k : Real) := by
    dsimp [p]
    field_simp [ne_of_gt hmR, ne_of_gt hkR]
  have hqMul : (k : Real) * (p / (m : Real))⁻¹ = (m : Real) := by
    rw [hqInv]
    field_simp [ne_of_gt hkR]
  have hlowroot :
      ((selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ k) ^
        (p / (m : Real))⁻¹ =
      (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) ^ m := by
    rw [← Real.rpow_natCast
        (selectedLowHC46NormBound (d := c + s) (r := r) (p := k) eta) k,
      ← Real.rpow_mul hCsum0, hqMul,
      Real.rpow_natCast]
  have hlowpow2 := Real.rpow_le_rpow hlowMoment0 hlowMoment' hq0
  have hlowpow' := hlowpow.trans (hlowpow2.trans_eq hlowroot)
  have hbetaexp0 : 0 ≤ beta ^ (1 - (p / (m : Real))⁻¹) :=
    Real.rpow_nonneg hbeta0 _
  have hlowfactor := mul_le_mul_of_nonneg_left hlowpow' hbetaexp0
  have hscaleLow := mul_le_mul_of_nonneg_left hlowfactor (by positivity : 0 ≤ (2 : Real) ^ m)
  have hbase := selected_actual_reconstructed_holder_bound
    (r := r) (m := m) C T f a p ha hp hdim
  have hhigh := selected_leaf_high_energy_le_spectral sourceHeightCutoff
    (T := T) (f := f) (r := r) hEven hRho hc hs hHeight hSpectral
  have hscaleHigh := mul_le_mul_of_nonneg_left hhigh
    (by positivity : 0 ≤ (1 / a ^ 2 : Real))
  dsimp [p, beta] at hbase hscaleLow hscaleHigh ⊢
  calc
    selectedActualMoment (m := m) (selectedG C f) (selectedF T f) ≤ _ := hbase
    _ ≤ _ := by
      exact add_le_add (add_le_add hscaleLow le_rfl) hscaleHigh

/-! Scalar right-hand side of the actual finite-level HC/spectral estimate. -/

theorem selected_actual_material_moment_bound_at_dyadic_exponent
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
    (hHC : HC46ExactContract)
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
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
  intro h J c s n Cc Tc fc
  have hparams := selected_spectral_parameters base sourceHeightCutoff hsel
  rcases hparams with
    ⟨hm256, hh, hdiv, hhpos, hspos, hsplit, hrhoPos, hrho, hcReal, hsReal,
      hbaseFloor, hcutFloor⟩
  have hm : 0 < m := by omega
  have hlarge : h ^ 2 < J := by
    dsimp [h, J]
    simpa only [one_mul] using
      ((Nat.mul_le_mul_right ((ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) hA).trans_lt
        (SamplerParameters.numerator_lt_blocks samplerA
          (ActualCmmsaParameterReconciliation.hBlock L m)))
  have hle : h ≤ h ^ 2 := by
    simpa [pow_two] using Nat.le_mul_of_pos_left h hhpos
  have hdim : c + s ≤ n := by
    dsimp [n, c, s, h]
    omega
  have hPR :=
    ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
      (r := r) (d := c + s) hrd Tc fc e he hfail
  have hMoment := selected_actual_HC_spectral_moment_bound_at_dyadic_exponent
    (n := n) (c := c) (s := s) (m := m)
    sourceHeightCutoff (C := Cc) (T := Tc) (f := fc) (a := a) ha hm hkm
    hsplit hrhoPos hcReal hsReal hcutFloor hPR hkDyadic hHC hSpectral hdim
  have hMass :=
    ActualSelectedComplementSourceSizeAppendMoment.selected_actual_append_moment
      I copies U A C T f (analyticSourceHeightFloor base sourceHeightCutoff) hsel hA
  have hMassMoment :
      (ActualOrdinaryStarWeightedSelection.matchingStarMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C)
        (ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T) f : Real) ≤
        2 * selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) := by
    simpa [ActualFixedFunctionalAppendOperator.actualAppendRankImageMoment,
      selectedActualMoment, selectedG, selectedF,
      ActualFixedFunctionalAppendOperator.CoordinateAmbient, CoordAmbient] using hMass
  have hMomentRhs :
      selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) ≤
        selected_actual_analytic_rhs (n := n) (c := c) (s := s) (m := m)
          Cc Tc fc r k (2 * (e : Real)) a := by
    simpa [selected_actual_analytic_rhs] using hMoment
  have hfinal := hMassMoment.trans
    (mul_le_mul_of_nonneg_left hMomentRhs (by norm_num : (0 : Real) ≤ 2))
  have hCenter :=
    ActualSelectedComplementSourceSizeAppendMoment.selected_actual_center_identity
      I copies U A C f (analyticSourceHeightFloor base sourceHeightCutoff) hsel hA
  have hBeta := matching_center_mass_eq_grassmann_beta
    (V := CoordAmbient J) (c := c) (s := s) (m := m)
    (by simpa [CoordAmbient] using hdim) Cc fc
  have hCenterR :
      (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := A.1) (m := m) (Nat.le_add_right c s)
        (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA)
        (ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C) f : Real) =
        (ActualOrdinaryStarWeightedSelection.matchingCenterMass
        (V := CoordAmbient J) (m := m) (Nat.le_add_right c s)
        (ActualComplementCoordinateMassBridge.actualCoordinateDimensionBound
          I copies U A
          (selected_actual_source_dimension_bound I copies U A base sourceHeightCutoff hsel hA))
        Cc fc : Real) := by
    exact_mod_cast hCenter
  exact ⟨hfinal, hCenterR.trans hBeta⟩


theorem selected_actual_material_moment_bound_original_at_dyadic_exponent
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
    (hSpectral : Spectral47ExactContract sourceHeightCutoff)
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
  exact selected_actual_material_moment_bound_at_dyadic_exponent I copies U A C T f
    base sourceHeightCutoff hsel hA r hrd e he hfail
    ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact hSpectral a ha hkDyadic hkm

end
end PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment
