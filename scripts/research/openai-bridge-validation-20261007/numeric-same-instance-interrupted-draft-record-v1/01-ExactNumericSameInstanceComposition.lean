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
import Mathlib.Tactic

/-! Exact same-instance composition for the numeric NO argument.

This remains a source offer: no Lean command has been run on this file.
The only external analytic premise is the original unconditioned side-density
lower bound for the fixed occurrence, globally predrawn tables, and sampler.
-/

namespace PvNP.RealizableHardness.ExactNumericSameInstanceComposition

open PvNP.RealizableHardness
open ActualNumericNo
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
    _ = 1 := ActualStarAcceptedGoodMass.eventMass_univ μ

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

open ActualGlobalDensityBridge
open ActualTaggedComplementIncidence
open ActualTaggedComplementStarDensityBridge
open ActualTaggedConcreteStarLaw
open ActualTaggedFixedTableAcceptance
open ActualOrdinaryStarSelection
open ActualBinaryGrassmannIncidence

/-- Conditional exact-real inverse agreement for the original fixed tables.
The selected complement and the internally chosen functional are used
unchanged through the density, weighted-star, material-moment, and scalar
arguments. -/
theorem same_instance_real_inverse_agreement
    {N rows L m samplerA : Nat}
    (I : ActualOccurrenceAllocation.Instance N rows)
    (copies : Nat)
    (U : ActualTaggedConcreteStarLaw.TaggedGoodU I copies
      (SamplerParameters.blocks samplerA
        (ActualCmmsaParameterReconciliation.hBlock L m)))
    (C : ActualTaggedFixedTableAcceptance.TaggedCenterTable I copies)
    (T : ActualTaggedFixedTableAcceptance.TaggedLeafTable I copies)
    (base : Nat → Nat) (cutoff : Real → Nat)
    (hA : 1 ≤ samplerA)
    (hsel : ActualCmmsaAdmissibilitySelector.selector
      (ActualNumericExplicitHeight.numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (hside : Real.rpow 2
      (-(2 * (1 - 1000 * ActualSelectedSpectralParameters.actualSelectedRho m
        (ActualCmmsaParameterReconciliation.hBlock L m)) *
        (m : Real) * (ActualCmmsaParameterReconciliation.hBlock L m : Real))) ≤
      (ActualTaggedMZSideDraw.sideConditionalDensity I copies U
        (ActualStarFixedRhoDimensionGuard.leafT m
          (ActualCmmsaParameterReconciliation.hBlock L m))
        (ActualCmmsaParameterReconciliation.hBlock L m)
        (ActualStarFixedRhoDimensionGuard.leafK m
          (ActualCmmsaParameterReconciliation.hBlock L m)) C T : Real)) :
    ∃ A : ActualTaggedComplementIncidence.SideComplement I copies U,
      ∃ q : Nat,
      ∃ Q : Grass (ActualMaximalPairLadder.CoordAmbient
        (SamplerParameters.blocks samplerA
          (ActualCmmsaParameterReconciliation.hBlock L m))) q,
      ∃ P : ActualMaximalPairLadder.DecodedPair Q
        (ActualStarFixedRhoDimensionGuard.leafT m
          (ActualCmmsaParameterReconciliation.hBlock L m) +
         ActualStarFixedRhoDimensionGuard.leafK m
          (ActualCmmsaParameterReconciliation.hBlock L m)),
        q + ActualMaximalPairLadder.codim P.W =
            ActualNumericSourceHeight.numericRankThreshold m ∧
        Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 ∧
        Real.rpow 2
          (-2 * (1 - 1000 * ActualSelectedSpectralParameters.actualSelectedRho m
            (ActualCmmsaParameterReconciliation.hBlock L m) ^ 2) *
            (ActualCmmsaParameterReconciliation.hBlock L m : Real)) <
          (ActualMaximalPairLadder.agreement
            (fun X => ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateLeafTable
              I copies U A T X) Q P : Real) := by
  classical
  let h := ActualCmmsaParameterReconciliation.hBlock L m
  let J := SamplerParameters.blocks samplerA h
  let c := ActualStarFixedRhoDimensionGuard.leafT m h
  let s := ActualStarFixedRhoDimensionGuard.leafK m h
  let d := c + s
  let r := ActualNumericSourceHeight.numericRankThreshold m
  let E := ActualNumericNoScalar.badExponent m h
  let eRat : Rat := ActualNumericExactThreshold.successMargin E
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
    (ActualNumericExplicitHeight.numericBase base) cutoff hsel'
  rcases hheight with ⟨hm, hr, hbase, hcut, hdiv⟩
  have hparams := ActualSelectedSpectralParameters.selected_spectral_parameters
    (ActualNumericExplicitHeight.numericBase base) cutoff hsel'
  rcases hparams with
    ⟨_, hh, hdivParams, hhpos, _, hsplit, hrhoPos, hrhoEq, hcParamReal,
      hsParamReal, _, _⟩
  have hthreshold := ActualNumericExactThreshold.successMargin_badExponent_cast_eq_actualSelectedPower
    hm hdiv hhpos
  have hscore : (eRat : Rat) ≤
      ActualTaggedMZSideDraw.sideConditionalDensity I copies U c h s C T := by
    have hreal : ((eRat : Rat) : Real) ≤
        (ActualTaggedMZSideDraw.sideConditionalDensity I copies U c h s C T : Real) := by
      change ((ActualNumericExactThreshold.successMargin
        (ActualNumericNoScalar.badExponent m h) : Rat) : Real) ≤ _
      rw [hthreshold]
      exact hside
    exact_mod_cast hreal
  have hdimBase : h ^ 2 < J := by
    dsimp [J]
    calc
      h ^ 2 = 1 * h ^ 2 := by simp
      _ ≤ samplerA * h ^ 2 := Nat.mul_le_mul_right (h ^ 2) hA
      _ < SamplerParameters.blocks samplerA h := SamplerParameters.numerator_lt_blocks samplerA h
  have hleSquare : h ≤ h ^ 2 := by
    have : 1 ≤ h := by omega
    nlinarith [sq_nonneg ((h : Int) - 1)]
  have hJ : h ≤ J := by omega
  have hsplitNat : d = 2 * h := by dsimp [d, c, s]; exact hsplit
  have hct : c ≤ d := by dsimp [d]; omega
  have hcomp := ActualGlobalDensityBridge.exists_complement_with_star_density_ge
    (I := I) (copies := copies) (U := U) (t := c) (h := h) (k := s)
    (by rw [hsplit]; omega) hJ C T eRat hscore
  obtain ⟨A, hstarDensity⟩ := hcomp
  let CA := ActualTaggedComplementStarDensityBridge.transportedCenterTable I copies U A C
  let TA := ActualTaggedComplementStarDensityBridge.transportedLeafTable I copies U A T
  have hfinrank : Module.finrank (ZMod 2) A.1 = 2 * J :=
    ActualTaggedComplementIncidence.sideComplement_finrank I copies U A
  have hdim : d ≤ Module.finrank (ZMod 2) A.1 := by rw [hfinrank, hsplitNat]; omega
  have hcenter : Nonempty (Grass A.1 c) :=
    ActualBinaryGrassmannIncidence.grass_nonempty_of_le (by omega)
  have hleaf : ∀ K : Grass A.1 c, Nonempty (ActualSourceStarLaw.LeafOver K d) := by
    intro K
    exact ActualSourceStarLaw.extension_nonempty K (by rw [hsplitNat]; omega) hdim
  have hfixed := ActualStarFixedRhoDimensionGuard.fixedRho_ambient_dimension_guard
    hm hh hdiv hA
  have hguard : m * (d - c) + E + 2 ≤ Module.finrank (ZMod 2) A.1 - c := by
    rw [hfinrank, hsplitNat]
    dsimp [d, E]
    omega
  have hstarScore : eRat ≤ ActualChangedAmbient8SBoundary.StarDensity
      (k := m) hcenter hleaf CA TA := by
    simpa [ActualGlobalDensityBridge.transportedStarDensity, CA, TA] using hstarDensity
  obtain ⟨f, hsignalRat, hXleBetaRat⟩ :=
    ActualOrdinaryStarWeightedSelection.ordinary_star_selects_weighted_functional
      (V := A.1) (t := c) (d := d) (m := m) (E := E)
      (by omega) (by rw [hfinrank, hsplitNat]; omega) (by omega) hguard
      hcenter hleaf CA TA hstarScore
  let Xq := ActualOrdinaryStarWeightedSelection.matchingStarMass
    (V := A.1) (m := m) (by omega) (by rw [hfinrank, hsplitNat]; omega) CA TA f
  let betaq := ActualOrdinaryStarWeightedSelection.matchingCenterMass
    (V := A.1) (m := m) (by omega) (by rw [hfinrank, hsplitNat]; omega) CA f
  let X : Real := (Xq : Real)
  let beta : Real := (betaq : Real)
  let n := Module.finrank (ZMod 2) A.1
  let M : Rat := 2 ^ (n - (c + m * (d - c)))
  let B : Rat := 2 ^ (n - c)
  let F : Rat := 2 ^ n
  let eps : Real := (eRat : Real)
  have hguardCore : c + m * (d - c) ≤ n := by
    have h := hguard
    dsimp [n] at h
    omega
  have hMB := weighted_MB_cast (n := n) (t := c) (s := d - c) (m := m) hguardCore
  have hMF := weighted_MF_cast (n := n) (t := c) (s := d - c) (m := m) hguardCore
  have hsignalCast :
      (((eRat / 4) * (M / B) * betaq +
        (eRat / 4) * (M / F) : Rat) : Real) ≤ (Xq : Real) := by
    exact_mod_cast (by simpa [M, B, F, n, d] using hsignalRat.1)
  have hdc : d - c = s := by dsimp [d, c, s]; omega
  have hsignal :
      eps / 4 * Real.rpow 2 (-((m * (d - c) : Nat) : Real)) * beta +
        eps / 4 * Real.rpow 2 (-((c + m * (d - c) : Nat) : Real)) ≤ X := by
    dsimp [eps, X, beta, M, B, F, n, Xq, betaq] at hsignalCast
    push_cast at hsignalCast
    rw [hMB, hMF] at hsignalCast
    simpa [hdc] using hsignalCast
  have hXleBeta : X ≤ beta := by
    dsimp [X, beta, Xq, betaq]
    exact_mod_cast hXleBetaRat
  have hbeta0q : 0 ≤ betaq := by
    dsimp [betaq, ActualOrdinaryStarWeightedSelection.matchingCenterMass]
    exact ActualStarAcceptedGoodMass.eventMass_nonneg _ _
  have hbeta1q : betaq ≤ 1 := by
    dsimp [betaq, ActualOrdinaryStarWeightedSelection.matchingCenterMass]
    calc
      ActualFiniteLaw.eventMass _ _ ≤ ActualFiniteLaw.eventMass _ Finset.univ :=
        ActualStarAcceptedGoodMass.eventMass_mono _ (Finset.subset_univ _)
      _ = 1 := ActualStarAcceptedGoodMass.eventMass_univ _
  have hbeta0 : 0 ≤ beta := by exact_mod_cast hbeta0q
  have hbeta1 : beta ≤ 1 := by exact_mod_cast hbeta1q
  have hbetaLink :
      eps / 4 * Real.rpow 2 (-((c + m * (d - c) : Nat) : Real)) ≤ beta := by
    have hfirst : 0 ≤ eps / 4 * Real.rpow 2 (-((m * (d - c) : Nat) : Real)) * beta :=
      by positivity
    linarith [hsignal, hXleBeta]
  have heps : Real.rpow 2
      (-2 * (1 - 1000 * rho) * (m : Real) * (h : Real)) ≤ eps := by
    change Real.rpow 2
      (-2 * (1 - 1000 * rho) * (m : Real) * (h : Real)) ≤ (eRat : Real)
    dsimp [eRat, E, rho]
    exact le_of_eq hthreshold.symm
  let Tc := fun X0 => ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateLeafTable
    I copies U A T X0
  refine ⟨A, ?_⟩
  by_contra hNoA
  have hfailReal := all_zoom_failure_of_no_strict_real_witness Tc e0 hNoA
  have he0nonneg : 0 ≤ e0 := by
    dsimp [e0]
    positivity
  have hmax := ActualNumericNo.actualAgreementMaximum_cast_le_of_failure Tc e0
    he0nonneg hfailReal
  have eNonneg : 0 ≤ eRat := ActualNumericNo.actualAgreementMaximum_nonneg Tc
  have hfail := ActualNumericNo.actualAgreementMaximum_gives_hfail
    (d := d) (r := r) Tc
  have hrd : r < d := by rw [hsplitNat]; omega
  have hfail' : ∀ q (Q : Grass (ActualMaximalPairLadder.CoordAmbient J) q)
      (P : ActualMaximalPairLadder.DecodedPair Q d),
      q + ActualMaximalPairLadder.codim P.W = r →
      Fintype.card (ActualMaximalPairLadder.Zoom Q P) ≠ 0 →
      ActualMaximalPairLadder.agreement Tc Q P ≤ eRat := by
    intro q Q P hbudget hzoom
    exact_mod_cast hfail q Q P hbudget hzoom
  have heRat : (eRat : Real) ≤ e0 := by
    simpa [eRat] using hmax
  have htail := ActualNumericSourceHeight.fixed_numeric_tail_parameters
    (by omega) hr hdiv hA
  rcases htail with ⟨_, hbr, hambient⟩
  have hcut := ActualNumericExplicitHeight.numeric_scalar_cutoffs hm
    ((Nat.le_max_right (base m) (ActualNumericExplicitHeight.numericHnum m)).trans hbase)
  dsimp [ActualNumericExplicitHeight.numericScalarCutoffGuards] at hcut
  rcases hcut with ⟨hcutT, hcutTscale, hP4, hPscale, he0half', hAbsorbCut', hFinalCut'⟩
  have hrho : rho = 1 / (ActualStarFixedRhoDimensionGuard.bOf m : Real) := by
    dsimp [rho]
    exact hrhoEq
  have hrhoSmall : rho ≤ 1 / 4000 := by
    rw [hrho]
    have hb : 4000 ≤ ActualStarFixedRhoDimensionGuard.bOf m := by
      dsimp [ActualStarFixedRhoDimensionGuard.bOf]
      nlinarith [show 1 ≤ m by omega]
    exact (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by norm_num at hb ⊢; exact_mod_cast hb)
  have hrhoR : (r : Real) * rho = 10 * (m : Real) := by
    dsimp [r, rho, ActualNumericSourceHeight.numericRankThreshold,
      ActualStarFixedRhoDimensionGuard.bOf]
    field_simp
    <;> ring
  have hcReal' : (c : Real) = 2 * (1 - rho) * (h : Real) := by
    simpa [c, rho, h] using hcParamReal
  have hsReal' : (s : Real) = 2 * rho * (h : Real) := by
    simpa [s, rho, h] using hsParamReal
  have hdReal : d = c + (d - c) := by omega
  have he0 : e0 = Real.rpow 2
      (-2 * (1 - 1000 * rho ^ 2) * (h : Real)) := by rfl
  have he0half : e0 ≤ 1 / 2 := by
    simpa [e0, rho, hrho] using he0half'
  have hAbsorbCut : Real.log (32 * ActualNumericNoScalar.scalarD m r) / Real.log 2 ≤
        (((8 : Real) / 3) * m - 2 + (3996 * m + 2) * rho) * h := by
    simpa [rho, r, ActualNumericSourceHeight.numericRankThreshold,
      ActualNumericNoScalar.scalarD, ActualNumericExplicitHeight.numericT,
      ActualNumericExplicitHeight.numericK] using hAbsorbCut'
  have hFinalCut :
      (Real.log
        (16 * ActualNumericNoScalar.scalarK m r (ActualNumericExplicitHeight.numericK m)) /
          Real.log 2 +
          2 / (ActualNumericExplicitHeight.numericT m : Real)) /
        ActualNumericNoScalar.scalarLambda m rho
          (ActualNumericExplicitHeight.numericT m : Real) < h := by
    simpa [rho, r, ActualNumericSourceHeight.numericRankThreshold,
      ActualNumericNoScalar.scalarK, ActualNumericNoScalar.scalarLambda,
      ActualNumericExplicitHeight.numericT, ActualNumericExplicitHeight.numericK] using hFinalCut'
  let fc := ActualSelectedComplementManuscriptDyadicMoment.coordinateFunctional I copies U A f
  let Cc := ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateCenterTable I copies U A C
  have hmaterialPair := ActualSelectedComplementManuscriptDyadicMoment.selected_actual_material_moment_bound_at_dyadic_exponent
    I copies U A C T f (ActualNumericExplicitHeight.numericBase base) cutoff hsel' hA r hrd
    eRat eNonneg hfail' ActualBinaryMatrixHC46OriginalExactInhabitant.original_HC46_exact
    (ActualSelectedComplementSourceSizeSpectralApplication.sourceSize_spectral47_inhabited cutoff)
    (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h))
    (by positivity)
    (ActualNumericExplicitHeight.numericK_rounding m hm).2.2.2.2
    (ActualNumericExplicitHeight.numericK_rounding m hm).2.2.1
  rcases hmaterialPair with ⟨hMoment, hCenter⟩
  let k := ActualNumericExplicitHeight.numericK m
  have hMaterial : X ≤ ActualNumericNoScalar.materialScalarRhs m k beta
      (ActualNumericNoScalar.selectedLowHC46NormBound (d := d) (r := r) (p := k)
        (2 * (eRat : Real)))
      (ActualNumericNoScalar.actualWeightedHighEnergy
        (b := ActualSelectedComplementManuscriptDyadicMoment.selectedF Tc fc)
        (d := d) (r := r) (bdim := s - 1))
      (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) := by
    have hSource : X ≤ 2 * ActualSelectedComplementManuscriptDyadicMoment.selected_actual_analytic_rhs
        (n := 2 * J) (c := c) (s := s) (m := m) Cc Tc fc r k
        (2 * (eRat : Real))
        (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) := by
      simpa [X, Xq, ActualSelectedComplementManuscriptDyadicMoment.coordinateFunctional,
        ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateLeafTable,
        ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateCenterTable,
        h, J, c, s, d, k] using hMoment
    have hconverted := ActualNumericNoScalar.selected_actual_source_material_scalar
      (n := 2 * J) (c := c) (s := s) (m := m) (r := r) (k := k) hbr
      Cc Tc fc r k (2 * (eRat : Real))
      (Real.rpow 2 (-((2 : Real) / 3) * (r : Real) * rho * h)) X hSource
    have hCenterBeta : beta =
        (ActualOrdinaryStarWeightedSelection.matchingCenterMass
          (V := A.1) (m := m) (by omega) (by rw [hfinrank, hsplitNat]; omega) CA f : Real) := by
      simpa [beta, betaq, CA, h, J, c, s, d] using hCenter
    rw [hCenterBeta]
    simpa [ActualSelectedComplementManuscriptDyadicMoment.selectedF,
      ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateLeafTable,
      ActualSelectedComplementManuscriptDyadicMoment.selectedCoordinateCenterTable,
      h, J, c, s, d, k] using hconverted
  have hambient' : d + r * (s - 1) + 3 ≤ 2 * J := by
    simpa [d, c, s, r, h, J] using hambient
  have hfalse := ActualNumericNoScalar.conservative_material_scalar_contradiction
    (n := 2 * J) (d := d) (r := r) (m := m) (k := k) (c := c) (s := s) (h := h)
    (rho := rho) (T := (ActualNumericExplicitHeight.numericT m : Real))
    (e0 := e0) (eRat := (eRat : Real)) (eps := eps) (beta := beta) (X := X)
    (ActualSelectedComplementManuscriptDyadicMoment.selectedF Tc fc)
    (by omega) hhpos hrhoPos hrhoSmall hrhoR hcReal' hsReal' rfl
    (by exact_mod_cast hcutT) (by exact_mod_cast hcutTscale)
    (by exact_mod_cast hP4) (by exact_mod_cast hPscale)
    (by exact_mod_cast eNonneg) heRat he0 he0half hbeta0 hbeta1 hbetaLink heps hsignal hXleBeta
    hambient' hbr hAbsorbCut hFinalCut hMaterial
  exact False.elim hfalse

end
end PvNP.RealizableHardness.ExactNumericSameInstanceComposition
