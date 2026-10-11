import PvNP.RealizableHardness.ExactCoordinateNumericInverse
import PvNP.RealizableHardness.ActualRefreshGoodCover
import PvNP.RealizableHardness.ActualRefreshNumericPreservation
import PvNP.RealizableHardness.ActualDistinctAdviceAverage
import PvNP.RealizableHardness.ActualNumericRobustReal
import PvNP.RealizableHardness.ActualNumericExplicitHeight
import PvNP.RealizableHardness.ActualNumericSourceHeight
import PvNP.RealizableHardness.ActualSelectedSpectralParameters
import PvNP.RealizableHardness.ActualComplementCoordinateMassBridge
import PvNP.RealizableHardness.SamplerParameters
import Mathlib.Tactic

/-! Uncompiled assembly of the unchanged selected-coordinate inverse with the
actual one-refresh finite cover and distinct-advice average. -/

namespace PvNP.RealizableHardness.ActualSelectedRefreshCoverAverage

open PvNP.RealizableHardness
open ActualCmmsaAdmissibilitySelector ActualCmmsaParameterReconciliation
open ActualNumericExplicitHeight ActualNumericSourceHeight
open ActualSelectedSpectralParameters ActualNumericRobustReal
open ActualRefreshGoodCover ActualRefreshNumericPreservation
open NumericRefreshFormalOffer NumericRefreshTailOffer
open ActualDistinctAdviceAverage ActualStarAcceptedGoodMass
open ActualStarFixedRhoDimensionGuard ActualSourceStarLaw
open ActualDistinctAdviceCoverage ActualMaximalPairLadder
open ActualChangedAmbient8SBoundary ActualComplementCoordinateMassBridge
open SamplerParameters
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact selected numeric source instance yields the manuscript's
distinct-advice lower bound after one concrete preserving refresh. The only
mass input is the original ordinary-star density lower bound. -/
theorem selected_coordinate_refresh_cover_average
    {L m samplerA : Nat}
    (base : Nat -> Nat) (cutoff : Real -> Nat)
    (hA : 1 <= samplerA)
    (hsel : selector (numericSourceFloor base cutoff) L = (m : WithBot Nat))
    (hcenter : Nonempty (Grass
      (CoordAmbient (blocks samplerA (hBlock L m)))
      (leafT m (hBlock L m))) )
    (hleaf : forall K : Grass
      (CoordAmbient (blocks samplerA (hBlock L m)))
      (leafT m (hBlock L m)),
      Nonempty (LeafOver K
        (leafT m (hBlock L m) + leafK m (hBlock L m))))
    (C : CenterTable
      (V := CoordAmbient (blocks samplerA (hBlock L m)))
      (leafT m (hBlock L m)))
    (T : LeafTable
      (V := CoordAmbient (blocks samplerA (hBlock L m)))
      (leafT m (hBlock L m) + leafK m (hBlock L m)))
    (horiginal : 2 * successMargin (badExponent m (hBlock L m)) <=
      StarDensity (k := m) hcenter hleaf C T) :
    (successMargin (badExponent m (hBlock L m)) : Rat) /
        (4 * (m : Rat) * (2 : Rat) ^ (4 * (hBlock L m) ^ 2)) <
      ∑ a : Fin (numericRankThreshold m + 1),
        goodAdviceFraction (CoordAmbient (blocks samplerA (hBlock L m)))
          (leafT m (hBlock L m) + leafK m (hBlock L m))
          (numericRankThreshold m) T (refreshThreshold m (hBlock L m)) a := by
  classical
  let h := hBlock L m
  let V := CoordAmbient (blocks samplerA h)
  let t := leafT m h
  let s := leafK m h
  let d := t + s
  let r := numericRankThreshold m
  let S : Rat := successMargin (badExponent m h)
  let e : Real := refreshThreshold m h
  have hbaseEq := numericSourceBase_eq base
  have hsel' : selector
      (fun j => max (analyticSourceHeightFloor (numericBase base) cutoff j) (j + 2)) L =
        (m : WithBot Nat) := by
    simpa [numericSourceFloor, hbaseEq] using hsel
  have hheight := selected_numeric_height (numericBase base) cutoff
    (by simpa only [hbaseEq] using hsel')
  rcases hheight with ⟨hm, hr, hbase, _hcut, hdiv⟩
  have hh : numericHnum m <= h :=
    (Nat.le_max_right (base m) (numericHnum m)).trans hbase
  have hmpos : 0 < m := by omega
  have hparams := selected_spectral_parameters (numericBase base) cutoff hsel'
  rcases hparams with
    ⟨_, hhsmall, _hdivParams, _hhpos, _hspos, hsplit, _hrhoPos, hrhoEq,
      _hcReal, _hsReal, _, _⟩
  have hsplit' : d = 2 * h := by
    dsimp [d, t, s, h]
    exact hsplit
  have hrank : r <= d := by dsimp [r]; omega
  have hfinrank : Module.finrank (ZMod 2) V = 2 * blocks samplerA h := by
    simp [V, CoordAmbient]
  have hJ : h <= blocks samplerA h := by
    have hsq : h ^ 2 < blocks samplerA h := by
      calc
        h ^ 2 = 1 * h ^ 2 := by simp
        _ <= samplerA * h ^ 2 := Nat.mul_le_mul_right _ hA
        _ < blocks samplerA h := numerator_lt_blocks samplerA h
    have hpos : 1 <= h := by omega
    have hle : h <= h ^ 2 := by nlinarith
    omega
  have hdimV : d <= Module.finrank (ZMod 2) V := by
    rw [hsplit', hfinrank]
    omega
  have htd : t <= 2 * h := by rw [← hsplit']; exact Nat.le_add_right _ _
  have hnoise : 2 * (1 / (2 : Real) ^ (2 * h)) <= e / 2 := by
    dsimp [e]
    simpa [one_div] using (refresh_threshold_bounds hm hh).2
  have hepos : 0 < e := by
    dsimp [e]
    have hb := (refresh_threshold_bounds hm hh).1
    positivity
  have heq : e = Real.rpow 2
      (-2 * (1 - 1000 * actualSelectedRho m h ^ 2) * (h : Real)) := by
    dsimp [e, refreshThreshold]
    rw [hrhoEq]
    rfl
  let T2 : RefreshTable V (2 * h) := by
    simpa only [hsplit'] using T
  have hleaf2 : forall K : Grass V t, Nonempty (LeafOver K (2 * h)) := by
    intro K
    simpa only [hsplit'] using hleaf K
  have hbad := numeric_actual_failure_mass_lt_one
    (originalGoodZoomCover V (2 * h) r T2 e) hfinrank hm hh hA
  have hinverse : forall T' : RefreshTable V (2 * h),
      StarDensity (k := m) hcenter hleaf2 C T2 / 2 <=
        StarDensity (k := m) hcenter hleaf2 C T' ->
      exists a : Nat, exists Q : Grass V a, exists P : DecodedPair Q (2 * h),
        a + codim P.W = r ∧ Fintype.card (Zoom Q P) ≠ 0 ∧
          e < (agreement T' Q P : Real) := by
    intro T' hhalf
    let Tsum : LeafTable (V := V) d := by
      simpa only [hsplit'] using T'
    have hhalf' : StarDensity (k := m) hcenter hleaf C T / 2 <=
        StarDensity (k := m) hcenter hleaf C Tsum := by
      simpa only [T2, Tsum, hleaf2, hsplit'] using hhalf
    have hscore : S <= StarDensity (k := m) hcenter hleaf C Tsum := by
      dsimp [S]
      have horig' : 2 * successMargin (badExponent m h) <=
          StarDensity (k := m) hcenter hleaf C T := by
        simpa [h] using horiginal
      linarith
    obtain ⟨q, Q, P, hbudget, hzoom, hagree⟩ :=
      ExactCoordinateNumericInverse.fixed_coordinate_real_inverse_agreement
        base cutoff hA hsel hcenter hleaf C Tsum hscore
    refine ⟨q, Q, P, ?_, hzoom, ?_⟩
    · simpa [r, h, d] using hbudget
    · simpa [e, heq] using hagree
  have hcover := good_cover_mass_lower_bound
    V (2 * h) r htd hdimV hmpos hcenter hleaf2 C T2 e hepos
    (by simpa only [hsplit'] using hnoise) hinverse hbad
  have havg := summed_good_advice_fraction_density_lower
    V r T2 e (by omega) hdimV
    (StarDensity (k := m) hcenter hleaf2 C T2) hcover
  have hden : 0 < 8 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) := by positivity
  have hcompare : S / (4 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) <=
      StarDensity (k := m) hcenter hleaf2 C T2 /
        (8 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) := by
    have horig' : 2 * successMargin (badExponent m h) <=
        StarDensity (k := m) hcenter hleaf2 C T2 := by
      simpa only [T2, hleaf2, hsplit'] using horiginal
    have hsame : S / (4 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) =
        (2 * S) / (8 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) := by
      have hden4 : 4 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) ≠ 0 := by positivity
      have hden8 : 8 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2) ≠ 0 := by positivity
      field_simp [hden4, hden8]
      <;> ring
    rw [hsame]
    exact (div_le_div_iff_of_pos_right hden).2 (by simpa [S] using horig')
  have havg' :
      StarDensity (k := m) hcenter hleaf2 C T2 /
          (8 * (m : Rat) * (2 : Rat) ^ (4 * h ^ 2)) <
        ∑ a : Fin (r + 1), goodAdviceFraction V (2 * h) r T2 e a := by
    simpa [h, r, V, T2, e, hsplit'] using havg
  have hresult := lt_of_le_of_lt hcompare havg'
  simpa [S, h, r, V, d, e, hsplit'] using hresult

end
end PvNP.RealizableHardness.ActualSelectedRefreshCoverAverage
