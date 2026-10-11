import PvNP.RealizableHardness.ActualNumericNo
import PvNP.RealizableHardness.ActualNumericNoScalar
import PvNP.RealizableHardness.ActualNumericExactThreshold
import PvNP.RealizableHardness.ActualNumericExplicitHeight
import PvNP.RealizableHardness.ActualGlobalDensityBridge
import PvNP.RealizableHardness.ActualOrdinaryStarWeightedSelection
import PvNP.RealizableHardness.ActualSelectedComplementManuscriptDyadicMoment
import PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant
import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeSpectralApplication
import PvNP.RealizableHardness.ActualOccurrenceAllocation
import PvNP.RealizableHardness.ActualTaggedConcreteStarLaw
import PvNP.RealizableHardness.ActualTaggedFixedTableAcceptance
import PvNP.RealizableHardness.ActualTaggedComplementIncidence
import PvNP.RealizableHardness.ActualTaggedComplementStarDensityBridge
import PvNP.RealizableHardness.ActualStarAcceptedGoodMass
import PvNP.RealizableHardness.ActualFiniteLaw
import PvNP.RealizableHardness.GrassmannCounting
import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAnalyticMoment
import PvNP.RealizableHardness.ActualCmmsaAdmissibilitySelector
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualStarFixedRhoDimensionGuard
import PvNP.RealizableHardness.SamplerParameters
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
import PvNP.RealizableHardness.ActualSelectedComplementSourceSizeAppendMoment
import PvNP.RealizableHardness.ActualLeafLabelRankImageAlignment
import PvNP.RealizableHardness.ActualSourceStarLaw
import Mathlib.Tactic

/-! Fixed coordinate ambient inverse, universally quantified over ordinary tables.
Uncompiled translation of the recorded refresh-compatible argument. -/

namespace PvNP.RealizableHardness.ExactCoordinateNumericInverse

open PvNP.RealizableHardness
open ActualNumericNo
open GrassmannCounting
open ActualNumericNoScalar
open ActualNumericExplicitHeight
open ActualNumericSourceHeight
open ActualSelectedSpectralParameters
open ActualStarFixedRhoDimensionGuard
open ActualTaggedComplementStarDensityBridge
open ActualTaggedComplementIncidence
open ActualOrdinaryStarWeightedSelection
open ActualSelectedComplementManuscriptDyadicMoment
open ActualMaximalPairLadder
open ActualCmmsaParameterReconciliation
open SamplerParameters
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-- Exact rational power-ratio transport used to turn the weighted selector's
literal `M/B` and `M/F` into the real negative powers consumed by the scalar
estimate. -/
private theorem rat_pow_ratio_cast {a b : Nat} (hab : a ≤ b) :
    (((2 : Rat) ^ a / (2 : Rat) ^ b : Rat) : Real) =
      Real.rpow 2 (-((b - a : Nat) : Real)) := by
  have hden : (2 : Rat) ^ b ≠ 0 := by positivity
  have hrat : (2 : Rat) ^ a / (2 : Rat) ^ b =
      1 / (2 : Rat) ^ (b - a) := by
    apply (div_eq_iff hden).2
    field_simp
    have hexp : a + (b - a) = b := by omega
    rw [← pow_add, hexp]
  rw [hrat]
  push_cast
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
  rw [Real.rpow_natCast]
  simp [one_div]

private theorem weighted_MB_cast {n t s m : Nat}
    (hguard : t + m * s ≤ n) :
    ((((2 : Rat) ^ (n - (t + m * s))) /
        (2 : Rat) ^ (n - t) : Rat) : Real) =
      Real.rpow 2 (-((m * s : Nat) : Real)) := by
  have hsub : n - (t + m * s) ≤ n - t := by omega
  have hgap : (n - t) - (n - (t + m * s)) = m * s := by omega
  rw [rat_pow_ratio_cast hsub, hgap]

private theorem weighted_MF_cast {n t s m : Nat}
    (hguard : t + m * s ≤ n) :
    ((((2 : Rat) ^ (n - (t + m * s))) / (2 : Rat) ^ n : Rat) : Real) =
      Real.rpow 2 (-((t + m * s : Nat) : Real)) := by
  have hsub : n - (t + m * s) ≤ n := Nat.sub_le _ _
  have hgap : n - (n - (t + m * s)) = t + m * s := by omega
  rw [rat_pow_ratio_cast hsub, hgap]

private theorem eventMass_le_one {Ω : Type*} [Fintype Ω]
    (μ : ActualFiniteLaw.FiniteLaw Ω) (S : Finset Ω) :
    ActualFiniteLaw.eventMass μ S ≤ 1 := by
  calc
    ActualFiniteLaw.eventMass μ S ≤ ActualFiniteLaw.eventMass μ Finset.univ :=
      ActualStarAcceptedGoodMass.eventMass_mono μ (Finset.subset_univ S)
    _ = 1 := ActualFiniteLaw.eventMass_univ μ

/-- The real-threshold contradiction is exactly the all-zoom hypothesis
needed by the rational finite-maximum consumer. -/
private theorem all_zoom_failure_of_no_strict_real_witness
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    {d r : Nat} (T : (L : Grass V d) → Module.Dual (ZMod 2) L.val) (e0 : Real)
    (hNo : ¬ ∃ q : Nat, ∃ Q : Grass V q,
      ∃ P : ActualMaximalPairLadder.DecodedPair Q d,
        q + ActualMaximalPairLadder.codim P.W = r ∧
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 ∧
        e0 < (ActualMaximalPairLadder.agreement T Q P : Real)) :
    ∀ q (Q : Grass V q)
      (P : ActualMaximalPairLadder.DecodedPair Q d),
      q + ActualMaximalPairLadder.codim P.W = r →
      Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
      (ActualMaximalPairLadder.agreement T Q P : Real) ≤ e0 := by
  intro q Q P hbudget hzoom
  by_contra hnot
  exact hNo ⟨q, Q, P, hbudget, hzoom, lt_of_not_ge hnot⟩

open ActualSourceStarLaw
open ActualSelectedComplementSourceSizeAnalyticMoment

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

/-- The same fixed coordinate ambient and arbitrary ordinary tables are retained
through the complete weighted, material and scalar inverse argument. -/
theorem fixed_coordinate_real_inverse_agreement
    {L m samplerA : Nat}
    (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (ActualNumericExplicitHeight.numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (hcenter : Nonempty (Grass (ActualComplementCoordinateMassBridge.CoordAmbient (SamplerParameters.blocks samplerA (ActualCmmsaParameterReconciliation.hBlock L m))) (ActualStarFixedRhoDimensionGuard.leafT m (ActualCmmsaParameterReconciliation.hBlock L m))))
    (hleaf : forall K : Grass (ActualComplementCoordinateMassBridge.CoordAmbient (SamplerParameters.blocks samplerA (ActualCmmsaParameterReconciliation.hBlock L m))) (ActualStarFixedRhoDimensionGuard.leafT m (ActualCmmsaParameterReconciliation.hBlock L m)),
      Nonempty (ActualChangedAmbient8SBoundary.LeafOver K (ActualStarFixedRhoDimensionGuard.leafT m (ActualCmmsaParameterReconciliation.hBlock L m) + ActualStarFixedRhoDimensionGuard.leafK m (ActualCmmsaParameterReconciliation.hBlock L m))))
    (C : ActualSourceStarLaw.CenterTable (V := ActualComplementCoordinateMassBridge.CoordAmbient (SamplerParameters.blocks samplerA (ActualCmmsaParameterReconciliation.hBlock L m))) (ActualStarFixedRhoDimensionGuard.leafT m (ActualCmmsaParameterReconciliation.hBlock L m)))
    (T : ActualSourceStarLaw.LeafTable (V := ActualComplementCoordinateMassBridge.CoordAmbient (SamplerParameters.blocks samplerA (ActualCmmsaParameterReconciliation.hBlock L m))) (ActualStarFixedRhoDimensionGuard.leafT m (ActualCmmsaParameterReconciliation.hBlock L m) + ActualStarFixedRhoDimensionGuard.leafK m (ActualCmmsaParameterReconciliation.hBlock L m)))
    (hscore : ActualStarAcceptedGoodMass.successMargin
        (ActualStarFixedRhoDimensionGuard.badExponent m (ActualCmmsaParameterReconciliation.hBlock L m)) <=
      ActualChangedAmbient8SBoundary.StarDensity (k := m) hcenter hleaf C T) :
    exists q : Nat, exists Q : Grass (ActualComplementCoordinateMassBridge.CoordAmbient (SamplerParameters.blocks samplerA (ActualCmmsaParameterReconciliation.hBlock L m))) q,
      exists P : ActualMaximalPairLadder.DecodedPair Q (ActualStarFixedRhoDimensionGuard.leafT m (ActualCmmsaParameterReconciliation.hBlock L m) + ActualStarFixedRhoDimensionGuard.leafK m (ActualCmmsaParameterReconciliation.hBlock L m)),
        q + ActualMaximalPairLadder.codim P.W = ActualNumericSourceHeight.numericRankThreshold m /\
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) != 0 /\
        Real.rpow 2
          (-2 * (1 - 1000 * ActualSelectedSpectralParameters.actualSelectedRho m
            (ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) * (ActualCmmsaParameterReconciliation.hBlock L m : Real)) <
          (ActualMaximalPairLadder.agreement T Q P : Real) := by
  classical
  let h := ActualCmmsaParameterReconciliation.hBlock L m
  let J := SamplerParameters.blocks samplerA h
  let c := ActualStarFixedRhoDimensionGuard.leafT m h
  let s := ActualStarFixedRhoDimensionGuard.leafK m h
  let d := c + s
  let r := ActualNumericSourceHeight.numericRankThreshold m
  let E := ActualStarFixedRhoDimensionGuard.badExponent m h
  let epsRat : Rat := ActualStarAcceptedGoodMass.successMargin E
  let rho : Real := ActualSelectedSpectralParameters.actualSelectedRho m h
  let e0 : Real := Real.rpow 2 (-2 * (1 - 1000 * rho ^ 2) * (h : Real))
  have hbaseEq := ActualNumericExplicitHeight.numericSourceBase_eq base
  have hsel' : ActualCmmsaAdmissibilitySelector.selector
      (fun j => max
        (ActualSelectedSpectralParameters.analyticSourceHeightFloor
          (ActualNumericExplicitHeight.numericBase base) cutoff j)
        (j + 2)) L = (m : WithBot Nat) := by
    simpa [ActualNumericExplicitHeight.numericSourceFloor, hbaseEq] using hsel
  have hheight := ActualNumericSourceHeight.selected_numeric_height
    (ActualNumericExplicitHeight.numericBase base) cutoff
    (by simpa only [hbaseEq] using hsel')
  rcases hheight with ⟨hm, hr, hbase, hcutHeight, hdiv⟩
  have hmpos : 0 < m := by omega
  have hbpos : 0 < bOf m := by
    dsimp [bOf]
    positivity
  have hparams := ActualSelectedSpectralParameters.selected_spectral_parameters
    (ActualNumericExplicitHeight.numericBase base) cutoff hsel'
  rcases hparams with
    ⟨_, hh, _hdivParams, hhpos, hspos, hsplit, hrhoPos, hrhoEq, hcParamReal,
      hsParamReal, _, _⟩
  have hthreshold := ActualNumericExactThreshold.successMargin_badExponent_cast_eq_actualSelectedPower
    hm hdiv hhpos
  have hdimBase : h ^ 2 < J := by
    dsimp [J]
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ ≤ samplerA * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < SamplerParameters.blocks samplerA h := SamplerParameters.numerator_lt_blocks samplerA h
  have hleSquare : h ≤ h ^ 2 := by
    calc
      h = h * 1 := by simp
      _ ≤ h * h := Nat.mul_le_mul_left h (by omega)
      _ = h ^ 2 := by ring
  have hJ : h ≤ J := by omega
  have hsplitNat : d = 2 * h := by dsimp [d, c, s]; exact hsplit
  have hct : c ≤ d := by dsimp [d]; omega
  have hdc : d - c = s := by dsimp [d]; omega
  have hspos' : 0 < s := hspos
  let CA := C
  let TA := T
  have hfinrank : Module.finrank (ZMod 2)
      (ActualComplementCoordinateMassBridge.CoordAmbient J) = 2 * J := by
    simp [ActualComplementCoordinateMassBridge.CoordAmbient]
  have hdim : d <= Module.finrank (ZMod 2)
      (ActualComplementCoordinateMassBridge.CoordAmbient J) := by
    rw [hfinrank, hsplitNat]
    omega
  have hfixed := ActualStarFixedRhoDimensionGuard.fixedRho_ambient_dimension_guard
    hm hh hdiv hA
  change c + m * s + E + 2 ≤ 2 * J at hfixed
  have hguard : m * (d - c) + E + 2 ≤ Module.finrank (ZMod 2) (ActualComplementCoordinateMassBridge.CoordAmbient J) - c := by
    rw [hfinrank, hdc]
    omega
  have hstarScore : epsRat <= ActualChangedAmbient8SBoundary.StarDensity
      (k := m) hcenter hleaf CA TA := by
    simpa only [epsRat, E, h, CA, TA] using hscore
  obtain ⟨f, hsignalRat, hXleBetaRat⟩ :=
    ActualOrdinaryStarWeightedSelection.ordinary_star_selects_weighted_functional
      (V := (ActualComplementCoordinateMassBridge.CoordAmbient J)) (t := c) (d := d) (m := m) (E := E)
      (by omega) (by rw [hfinrank, hsplitNat]; omega) (by rw [hdc]; omega) hguard
      hcenter hleaf CA TA hstarScore
  let Xq := ActualOrdinaryStarWeightedSelection.matchingStarMass
    (V := (ActualComplementCoordinateMassBridge.CoordAmbient J)) (m := m) (by omega) (by rw [hfinrank, hsplitNat]; omega) CA TA f
  let betaq := ActualOrdinaryStarWeightedSelection.matchingCenterMass
    (V := (ActualComplementCoordinateMassBridge.CoordAmbient J)) (m := m) (by omega) (by rw [hfinrank, hsplitNat]; omega) CA f
  let X : Real := (Xq : Real)
  let beta : Real := (betaq : Real)
  let n := Module.finrank (ZMod 2) (ActualComplementCoordinateMassBridge.CoordAmbient J)
  let M : Rat := 2 ^ (n - (c + m * (d - c)))
  let B : Rat := 2 ^ (n - c)
  let F : Rat := 2 ^ n
  let eps : Real := (epsRat : Real)
  have hguardCore : c + m * (d - c) ≤ n := by
    have h := hguard
    dsimp [n] at h
    omega
  have hMB := weighted_MB_cast (n := n) (t := c) (s := d - c) (m := m) hguardCore
  have hMF := weighted_MF_cast (n := n) (t := c) (s := d - c) (m := m) hguardCore
  have hsignalCast :
      (((epsRat / 4) * (M / B) * betaq +
        (epsRat / 4) * (M / F) : Rat) : Real) ≤ (Xq : Real) := by
    exact_mod_cast (show epsRat / 4 * (M / B) * betaq +
        epsRat / 4 * (M / F) ≤ Xq from by
      simpa only [M, B, F, n, Xq, betaq, epsRat] using hsignalRat)
  have hquarter : ((epsRat / 4 : Rat) : Real) = eps / 4 := by simp [eps]
  have hMB' : ((M / B : Rat) : Real) =
      Real.rpow 2 (-((m * (d - c) : Nat) : Real)) := hMB
  have hMF' : ((M / F : Rat) : Real) =
      Real.rpow 2 (-((c + m * (d - c) : Nat) : Real)) := hMF
  have hsignal :
      eps / 4 * Real.rpow 2 (-(m * s : Real)) * beta +
        eps / 4 * Real.rpow 2 (-(c + m * s : Real)) ≤ X := by
    simpa only [Rat.cast_add, Rat.cast_mul, hquarter, hMB', hMF',
      hdc, Nat.cast_add, Nat.cast_mul] using hsignalCast
  have hXleBeta : X ≤ beta := by
    dsimp [X, beta, Xq, betaq]
    exact_mod_cast hXleBetaRat
  have hbeta0q : 0 ≤ betaq := by
    dsimp [betaq, ActualOrdinaryStarWeightedSelection.matchingCenterMass]
    exact ActualStarAcceptedGoodMass.eventMass_nonneg _ _
  have hbeta1q : betaq ≤ 1 := by
    dsimp [betaq, ActualOrdinaryStarWeightedSelection.matchingCenterMass]
    exact eventMass_le_one _ _
  have hbeta0 : 0 ≤ beta := by exact_mod_cast hbeta0q
  have hbeta1 : beta ≤ 1 := by exact_mod_cast hbeta1q
  have heps0 : 0 ≤ eps := by
    dsimp [eps, epsRat, ActualStarAcceptedGoodMass.successMargin]
    positivity
  have hbetaLink :
      eps / 4 * Real.rpow 2 (-(c + m * s : Real)) ≤ beta := by
    have hfirst : 0 ≤ eps / 4 * Real.rpow 2 (-(m * s : Real)) * beta :=
      by positivity
    linarith [hsignal, hXleBeta]
  have heps : Real.rpow 2
      (-2 * (1 - 1000 * rho) * (m : Real) * (h : Real)) ≤ eps := by
    change Real.rpow 2
      (-2 * (1 - 1000 * rho) * (m : Real) * (h : Real)) ≤ (epsRat : Real)
    dsimp [epsRat, E, rho]
    simpa only [neg_mul] using le_of_eq hthreshold.symm
  let Tc := T
  let etaRat : Rat := ActualNumericNo.actualAgreementMaximum (r := r) Tc
  by_contra hNoA
  have hfailReal := all_zoom_failure_of_no_strict_real_witness Tc e0 hNoA
  have he0nonneg : 0 ≤ e0 := by
    dsimp [e0]
    positivity
  have hmax := ActualNumericNo.actualAgreementMaximum_cast_le_of_failure (r := r) Tc e0
    he0nonneg hfailReal
  have eNonneg : 0 ≤ etaRat := ActualNumericNo.actualAgreementMaximum_nonneg (r := r) Tc
  have hfail := ActualNumericNo.actualAgreementMaximum_gives_hfail
    (d := d) (r := r) Tc
  have hrd : r < d := by rw [hsplitNat]; omega
  have hfail' : ∀ q (Q : Grass (ActualComplementCoordinateMassBridge.CoordAmbient J) q)
      (P : ActualMaximalPairLadder.DecodedPair Q d),
      q + ActualMaximalPairLadder.codim P.W = r →
      Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
      ActualMaximalPairLadder.agreement Tc Q P ≤ etaRat := by
    intro q Q P hbudget hzoom
    exact_mod_cast hfail q Q P hbudget hzoom
  have heRat : (etaRat : Real) ≤ e0 := by
    simpa [etaRat] using hmax
  have htail := ActualNumericSourceHeight.fixed_numeric_tail_parameters
    (by omega) hr hdiv hA
  rcases htail with ⟨_, hbr, hambient⟩
  have hcut := ActualNumericExplicitHeight.numeric_scalar_cutoffs hm
    ((Nat.le_max_right (base m) (ActualNumericExplicitHeight.numericHnum m)).trans hbase)
  dsimp [ActualNumericExplicitHeight.numericScalarCutoffGuards] at hcut
  rcases hcut with ⟨hcutT, hcutTscale, hP4, hPscale, he0half', hAbsorbCut', hFinalCut'⟩
  have hrho : rho = 1 / (ActualCmmsaParameterReconciliation.bOf m : Real) := by
    dsimp [rho]
    exact hrhoEq
  have hrhoSmall : rho ≤ 1 / 4000 := by
    rw [hrho]
    have hb : 4000 ≤ ActualCmmsaParameterReconciliation.bOf m := by
      dsimp [ActualCmmsaParameterReconciliation.bOf]
      nlinarith [show 1 ≤ m by omega]
    exact (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by norm_num at hb ⊢; exact_mod_cast hb)
  have hrhoR : (r : Real) * rho = 10 * (m : Real) := by
    rw [hrho]
    dsimp [r, ActualNumericSourceHeight.numericRankThreshold]
    push_cast
    field_simp [show (bOf m : Real) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hbpos)] <;> ring
  have hcReal' : (c : Real) = 2 * (1 - rho) * (h : Real) := by
    simpa [c, rho, h] using hcParamReal
  have hsReal' : (s : Real) = 2 * rho * (h : Real) := by
    simpa [s, rho, h] using hsParamReal
  have he0 : e0 = Real.rpow 2
      (-2 * (1 - 1000 * rho ^ 2) * (h : Real)) := by rfl
  have he0half : e0 ≤ 1 / 2 := by
    simpa only [e0, hrho] using he0half'
  have hAbsorbCut : Real.log (32 * ActualNumericNoScalar.scalarD m r) / Real.log 2 ≤
        (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h := by
    simpa only [hrho, r] using hAbsorbCut'
  have hFinalCut :
      (Real.log
        (16 * ActualNumericNoScalar.scalarK m r (ActualNumericExplicitHeight.numericK m)) /
          Real.log 2 +
          2 / (ActualNumericExplicitHeight.numericT m : Real)) /
        ActualNumericNoScalar.scalarLambda m rho
          (ActualNumericExplicitHeight.numericT m : Real) < h := by
    simpa only [hrho, r] using hFinalCut'
  let fc := f
  let Cc := C
  let k := ActualNumericExplicitHeight.numericK m
  have hPR := ActualLeafLabelRankImageAlignment.actual_leaf_failed_zoom_gives_nominal_pseudorandom
    (r := r) (d := d) hrd Tc fc etaRat eNonneg hfail'
  have hdimN : c + s <= 2 * J := by
    have hd := hdim
    rw [hfinrank] at hd
    exact hd
  have hMomentMatrix :=
    ActualSelectedComplementManuscriptDyadicMoment.selected_actual_HC_spectral_moment_bound_at_dyadic_exponent
      (n := 2 * J) (c := c) (s := s) (m := m) (r := r) (k := k)
      cutoff (C := Cc) (T := Tc) (f := fc)
      (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h))
      (by positivity) hmpos
      (ActualNumericExplicitHeight.numericK_rounding m hm).2.2.1
      hsplit hrhoPos hcParamReal hsParamReal hcutHeight hPR
      (ActualNumericExplicitHeight.numericK_rounding m hm).2.2.2
      ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact
      (ActualSelectedComplementSourceSizeSpectralApplication.sourceSize_spectral47_inhabited cutoff)
      hdimN
  have hbudget : c + s = 2 * h /\ c + m * s + 2 * h <= 2 * J :=
    selected_rankloss_exponent hm hh hA rfl rfl rfl
  have hsmall := rankloss_from_exponent hhpos hbudget.1 hbudget.2
  have hsmall' : ((c + m * s : Nat) : Real) * (2 : Real) ^ (c + s - 1) /
      (2 : Real) ^ Module.finrank (ZMod 2)
        (ActualFixedFunctionalAppendOperator.CoordinateAmbient (2 * J)) <= 1 / 2 := by
    simpa only [show Module.finrank (ZMod 2)
      (ActualFixedFunctionalAppendOperator.CoordinateAmbient (2 * J)) = 2 * J by
        simp [ActualFixedFunctionalAppendOperator.CoordinateAmbient]] using hsmall
  have hAppend := ActualFixedFunctionalAppendOperator.matchingStarMass_cast_le_twice_actualAppendRankImageMoment
    (n := 2 * J) (c := c) (s := s) (k := m) hdim
    (by rw [hbudget.1]; omega) hsmall' Cc Tc fc
  have hMassMoment : X <= 2 * selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) := by
    simpa [X, Xq, CA, TA, Cc, Tc, fc,
      ActualFixedFunctionalAppendOperator.actualAppendRankImageMoment,
      selectedActualMoment, selectedG, selectedF,
      ActualFixedFunctionalAppendOperator.CoordinateAmbient,
      ActualComplementCoordinateMassBridge.CoordAmbient] using hAppend
  have hMomentRhs : selectedActualMoment (m := m) (selectedG Cc fc) (selectedF Tc fc) <=
      selected_actual_analytic_rhs (n := 2 * J) (c := c) (s := s) (m := m)
        Cc Tc fc r k (2 * (etaRat : Real))
        (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) := by
    simpa [selected_actual_analytic_rhs] using hMomentMatrix
  have hMoment := hMassMoment.trans
    (mul_le_mul_of_nonneg_left hMomentRhs (by norm_num : (0 : Real) <= 2))
  have hCenter := matching_center_mass_eq_grassmann_beta
    (V := ActualComplementCoordinateMassBridge.CoordAmbient J)
    (c := c) (s := s) (m := m) hdim Cc fc
  have hMaterial : X ≤ ActualNumericNoScalar.materialScalarRhs m k beta
      (ActualSelectedComplementSourceSizeAnalyticMoment.selectedLowHC46NormBound (d := d) (r := r) (p := k)
        (2 * (etaRat : Real)))
      (ActualNumericNo.actualWeightedHighEnergy
        (b := ActualSelectedComplementSourceSizeAnalyticMoment.selectedF Tc fc)
        (d := d) (r := r) (bdim := s - 1))
      (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) := by
    have hSource : X ≤ 2 * ActualSelectedComplementSourceSizeAnalyticMoment.selected_actual_analytic_rhs
        (n := 2 * J) (c := c) (s := s) (m := m) Cc Tc fc r k
        (2 * (etaRat : Real))
        (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) := by
      simpa only [X, Xq, CA, TA, Cc, Tc, fc, h, J, c, s, d, k] using hMoment
    have hconverted := ActualNumericNoScalar.selected_actual_source_material_scalar
      (n := 2 * J) (c := c) (s := s) (m := m) (r := r) (k := k) hbr
      Cc Tc fc (2 * (etaRat : Real))
      (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) X hSource
    have hCenterBeta : beta =
        (∑ R : Grass (ActualComplementCoordinateMassBridge.CoordAmbient J) c,
          if ActualFixedFunctionalStarMoment.centerMatchBit Cc fc R then (1 : Real) else 0) /
            (Fintype.card (Grass (ActualComplementCoordinateMassBridge.CoordAmbient J) c) : Real) := by
      simpa only [beta, betaq, CA, Cc, fc, h, J, c, s, d] using hCenter
    rw [hCenterBeta]
    simpa only [h, J, c, s, d, k] using hconverted
  have hambient' : d + r * (s - 1) + 3 ≤ 2 * J := by
    simpa [d, c, s, r, h, J] using hambient
  have hfalse := ActualNumericNoScalar.conservative_material_scalar_contradiction
    (n := 2 * J) (d := d) (r := r) (m := m) (k := k) (c := c) (s := s) (h := h)
    (rho := rho) (T := (ActualNumericExplicitHeight.numericT m : Real))
    (e0 := e0) (eRat := (etaRat : Real)) (eps := eps) (beta := beta) (X := X)
    (ActualSelectedComplementSourceSizeAnalyticMoment.selectedF Tc fc)
    (by omega) hhpos hrhoPos hrhoSmall hrhoR hcReal' hsReal' rfl
    (by exact_mod_cast hcutT) (by simpa only [hrho] using hcutTscale)
    (by exact_mod_cast hP4) (by exact_mod_cast hPscale)
    (by exact_mod_cast eNonneg) heRat he0 he0half hbeta0 hbeta1 hbetaLink heps hsignal hXleBeta
    hambient' hbr hAbsorbCut hFinalCut hMaterial
  exact False.elim hfalse


end
end PvNP.RealizableHardness.ExactCoordinateNumericInverse
