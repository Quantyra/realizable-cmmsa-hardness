import PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46PositiveColumns

open PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant
open ActualBinaryMatrixHC46RealQNorm ActualBinaryMatrixHC46RealQTransport
open ActualBinaryMatrixHC46BooleanGlobalness ActualBinaryMatrixHC46
open ActualBinaryMatrixHC46A22OriginalInduction
open ActualBinaryMatrixHC46A18OriginalGlobalInduction
open ActualBinaryMatrixHC46A18InductionBounds ActualBinaryMatrixHC46A21DyadicMoment
open ActualFiniteDegreeFourierReconstruction ActualSelectedComplementAnalyticMoment
open BinaryMatrixFourier BinaryMatrixA1Complex BinaryMatrixComplexA14 BinaryMatrixComplexA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual positive-rank branch of the inherited Boolean HC46 proof,
with arbitrary column dimension. Only the rank-zero branch uses the even-column
hypothesis; the A22/A18/A21 proof engine and all its assumptions are retained. -/
theorem hc46_positive_rank_arbitrary_columns {n d r i p : Nat} {eta : Real}
    (b : BinaryMatrix n d → Bool)
    (hPR : PseudorandomExact r eta b) (hi : i ≤ r) (hiPos : 0 < i)
    (hp4 : 4 ≤ p) (hdyadic : exists q : Nat, p = 2 ^ q) :
    lpNorm p (rankProjection i (indicator b)) ≤
      (2 : Real) ^ (500 * i ^ 2 * p) * eta ^ (((p : Real) - 2) / (p : Real)) := by
  have heta : 0 ≤ eta :=
    (uniformMean_indicator_nonneg b).trans (boolean_mean_le_of_exact b hPR)
  let delta := min eta 1
  have hdelta : 0 ≤ delta := le_min heta (by norm_num)
  have hdelta1 : delta ≤ 1 := min_le_right _ _
  have hmean : uniformMean (indicator b) ≤ delta :=
    le_min (boolean_mean_le_of_exact b hPR) (original_HC46_boolean_mean_le_one b)
  let f := booleanIndicatorComplex b
  let g := complexRankProjection i f
  have hfEnergy : a22Energy f ≤ delta := by
    rw [original_HC46_boolean_second]
    exact hmean
  have hprojection : a22Energy g ≤ delta := (a22_projection_energy_le f).trans hfEnergy
  have hmomentEq : lpMoment p (fun M => ‖g M‖) =
      lpMoment p (rankProjection i (indicator b)) := by
    unfold lpMoment
    congr 1
    funext M
    simp only [g, f, complexRankProjection_boolean_eq, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  by_cases hd0 : delta = 0
  · have hf0 : f = 0 := original_HC46_boolean_zero_of_energy_zero b
      (le_antisymm (by simpa only [hd0] using hfEnergy) (a22_energy_nonneg f))
    have hreal0 : indicator b = 0 := by
      funext M
      have hz := congrArg (fun u : BinaryMatrix n d → Complex => (u M).re) hf0
      simpa only [f, booleanIndicatorComplex, Complex.ofReal_re, Pi.zero_apply, Complex.zero_re] using hz
    have hnorm0 : lpNorm p (rankProjection i (indicator b)) = 0 := by
      rw [hreal0]
      simp [rankProjection, fourierCoeff, uniformMean, lpMoment, lpNorm]
      rw [zero_pow (by omega : p ≠ 0),
        Real.zero_rpow (by positivity : (p : Real)⁻¹ ≠ 0)]
    rw [hnorm0]
    positivity
  have hdpos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hd0)
  have hp2 : 2 ≤ p := by omega
  have hLq := exactPR_to_actual_LqGlobal b hp2 hPR
  have hLqi : UpToActualLqGlobal i (pConjugate p) (delta ^ (1 - 1 / (p : Real))) f := by
    intro Q hQ
    exact hLq Q (hQ.trans hi)
  have hinfl := manuscript_A22_actual f hLqi hp2 hdyadic
  have hsupport := complexRankProjection_supportedThrough (D := i) le_rfl f
  have hglobal := actual_A18_original_global (r := i) g hsupport hinfl
  have hscale : a18BudgetScale i i
      ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ (1 - 1 / (p : Real))) ^ 2) =
      (2 : Real) ^ (10 * i ^ 2) *
        ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ (1 - 1 / (p : Real))) ^ 2) := by
    unfold a18BudgetScale
    congr 1
    congr 1
    ring
  have hglobal' : UpToActualNormSqGlobal i
      ((2 : Real) ^ (10 * i ^ 2) *
        ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ (1 - 1 / (p : Real))) ^ 2)) g := by
    simpa only [hscale] using hglobal
  have hmoment := manuscript_A21_actual g hsupport hglobal' hp2 hdyadic
  have hmoment' : lpMoment p (rankProjection i (indicator b)) ≤
      (2 : Real) ^ (500 * i ^ 2 * p ^ 2) * delta ^ (p - 2) := by
    rw [← hmomentEq]
    apply hmoment.trans
    calc
      _ ≤ (2 : Real) ^ (200 * i ^ 2 * p ^ 2) * delta *
          ((2 : Real) ^ (10 * i ^ 2) *
            ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ (1 - 1 / (p : Real))) ^ 2)) ^
              (p / 2 - 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hprojection (by positivity)
      _ ≤ _ := original_HC46_moment_density_algebra hp4
        (a22_dyadic_even hp2 hdyadic).2 hdpos hdelta1
  have hnorm := original_HC46_moment_to_norm (rankProjection i (indicator b)) hp4 hdelta hmoment'
  apply hnorm.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow hdelta (min_le_left eta 1)
  have hpReal : (4 : Real) ≤ (p : Real) := by exact_mod_cast hp4
  exact div_nonneg (by linarith) (by positivity)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46PositiveColumns
