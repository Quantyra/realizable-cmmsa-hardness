import PvNP.RealizableHardness.ActualBinaryMatrixHC46A22OriginalInduction
import PvNP.RealizableHardness.ActualBinaryMatrixHC46BooleanGlobalness
import PvNP.RealizableHardness.ActualSelectedComplementAnalyticMoment

/-! The unchanged exact nominal-budget HC46 contract, including unrestricted
eta. The Boolean density cap is derived internally and the actual A22/A18/A21
chain is used without an analytic oracle or basis-invariance hypothesis. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant
open ActualBinaryMatrixHC46A22OriginalInduction
open ActualBinaryMatrixHC46RealQNorm ActualBinaryMatrixHC46RealQTransport
open ActualBinaryMatrixHC46BooleanGlobalness ActualBinaryMatrixHC46
open ActualBinaryMatrixHC46A18OriginalGlobalInduction
open ActualBinaryMatrixHC46A18InductionBounds ActualBinaryMatrixHC46A21DyadicMoment
open ActualFiniteDegreeFourierReconstruction ActualSelectedComplementAnalyticMoment
open BinaryMatrixFourier BinaryMatrixA1Complex BinaryMatrixComplexA14 BinaryMatrixComplexA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

theorem original_HC46_boolean_second {n d : Nat} (b : BinaryMatrix n d → Bool) :
    a22Energy (booleanIndicatorComplex b) = uniformMean (indicator b) := by
  unfold a22Energy
  congr 1
  funext M
  by_cases hb : b M = true <;> simp [booleanIndicatorComplex, indicator, hb]

theorem original_HC46_boolean_mean_le_one {n d : Nat} (b : BinaryMatrix n d → Bool) :
    uniformMean (indicator b) ≤ 1 := by
  have hcard : 0 < (Fintype.card (BinaryMatrix n d) : Real) := by positivity
  unfold uniformMean
  rw [div_le_iff₀ hcard]
  calc
    (∑ M : BinaryMatrix n d, indicator b M) ≤ ∑ _M : BinaryMatrix n d, (1 : Real) := by
      apply Finset.sum_le_sum
      intro M _
      by_cases hb : b M = true <;> simp [indicator, hb]
    _ = _ := by simp

theorem original_HC46_boolean_zero_of_energy_zero {n d : Nat}
    (b : BinaryMatrix n d → Bool) (hz : a22Energy (booleanIndicatorComplex b) = 0) :
    booleanIndicatorComplex b = 0 := by
  have hc : (Fintype.card (BinaryMatrix n d) : Real) ≠ 0 := by positivity
  unfold a22Energy uniformMean at hz
  have hs : (∑ M : BinaryMatrix n d, Complex.normSq (booleanIndicatorComplex b M)) = 0 := by
    simpa using (div_eq_iff hc).mp hz
  funext M
  have hsingle : Complex.normSq (booleanIndicatorComplex b M) ≤ 0 := by
    rw [← hs]
    exact Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ M)
  exact Complex.normSq_eq_zero.mp (le_antisymm hsingle (Complex.normSq_nonneg _))

theorem original_HC46_moment_density_algebra {i p : Nat} {delta : Real}
    (hp : 4 ≤ p) (hpEven : p = 2 * (p / 2)) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    (2 : Real) ^ (200 * i ^ 2 * p ^ 2) * delta *
      ((2 : Real) ^ (10 * i ^ 2) *
        ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ (1 - 1 / (p : Real))) ^ 2)) ^
          (p / 2 - 1) ≤
      (2 : Real) ^ (500 * i ^ 2 * p ^ 2) * delta ^ (p - 2) := by
  let m := p / 2 - 1
  let a : Real := 1 - 1 / (p : Real)
  have hp0 : 0 < (p : Real) := by exact_mod_cast (by omega : 0 < p)
  have hm : 2 * (m + 1) = p := by dsimp [m]; omega
  have hcoefficient : 200 * i ^ 2 * p ^ 2 + (10 * i ^ 2 + 500 * i ^ 2 * p) * m ≤
      500 * i ^ 2 * p ^ 2 := by
    have hm2 : 2 * m ≤ p := by omega
    have hmp := Nat.mul_le_mul_left (5 * i ^ 2 + 250 * i ^ 2 * p) hm2
    have hpp : p ≤ p ^ 2 := by nlinarith
    have hsmall := Nat.mul_le_mul_left (5 * i ^ 2) hpp
    calc
      _ = 200 * i ^ 2 * p ^ 2 + (5 * i ^ 2 + 250 * i ^ 2 * p) * (2 * m) := by ring
      _ ≤ 200 * i ^ 2 * p ^ 2 + (5 * i ^ 2 + 250 * i ^ 2 * p) * p :=
        Nat.add_le_add_left hmp _
      _ = 450 * i ^ 2 * p ^ 2 + 5 * i ^ 2 * p := by ring
      _ ≤ 450 * i ^ 2 * p ^ 2 + 5 * i ^ 2 * p ^ 2 := Nat.add_le_add_left hsmall _
      _ = 455 * (i ^ 2 * p ^ 2) := by ring
      _ ≤ 500 * (i ^ 2 * p ^ 2) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring
  have hdensity : ((p - 2 : Nat) : Real) ≤ 1 + a * ((2 * m : Nat) : Real) := by
    have hmReal : (2 : Real) * ((m : Real) + 1) = (p : Real) := by exact_mod_cast hm
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    push_cast
    dsimp [a]
    field_simp
    nlinarith
  have hpower :
      (2 : Real) ^ (200 * i ^ 2 * p ^ 2) *
        ((2 : Real) ^ (10 * i ^ 2)) ^ m * ((2 : Real) ^ (500 * i ^ 2 * p)) ^ m =
      (2 : Real) ^ (200 * i ^ 2 * p ^ 2 + (10 * i ^ 2 + 500 * i ^ 2 * p) * m) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  have hdeltaPower : ((delta ^ a) ^ 2) ^ m = delta ^ (a * ((2 * m : Nat) : Real)) := by
    rw [← pow_mul, ← Real.rpow_mul_natCast (le_of_lt hdelta)]
  have hnormalize :
      (2 : Real) ^ (200 * i ^ 2 * p ^ 2) * delta *
        ((2 : Real) ^ (10 * i ^ 2) *
          ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ a) ^ 2)) ^ m =
      (2 : Real) ^ (200 * i ^ 2 * p ^ 2 + (10 * i ^ 2 + 500 * i ^ 2 * p) * m) *
        delta ^ (1 + a * ((2 * m : Nat) : Real)) := by
    rw [mul_pow ((2 : Real) ^ (10 * i ^ 2))
        ((2 : Real) ^ (500 * i ^ 2 * p) * (delta ^ a) ^ 2) m,
      mul_pow ((2 : Real) ^ (500 * i ^ 2 * p)) ((delta ^ a) ^ 2) m, hdeltaPower]
    rw [Real.rpow_add hdelta, Real.rpow_one]
    calc
      _ = ((2 : Real) ^ (200 * i ^ 2 * p ^ 2) *
          ((2 : Real) ^ (10 * i ^ 2)) ^ m * ((2 : Real) ^ (500 * i ^ 2 * p)) ^ m) *
          (delta * delta ^ (a * ((2 * m : Nat) : Real))) := by ring
      _ = _ := by rw [hpower]
  rw [hnormalize]
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hcoefficient
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 hdensity
  · exact Real.rpow_nonneg (le_of_lt hdelta) _
  · positivity

theorem original_HC46_moment_to_norm {n d i p : Nat} {delta : Real}
    (F : BinaryMatrix n d → Real) (hp : 4 ≤ p) (hdelta : 0 ≤ delta)
    (hmoment : lpMoment p F ≤ (2 : Real) ^ (500 * i ^ 2 * p ^ 2) * delta ^ (p - 2)) :
    lpNorm p F ≤ (2 : Real) ^ (500 * i ^ 2 * p) *
      delta ^ (((p : Real) - 2) / (p : Real)) := by
  have hp0 : 0 < (p : Real) := by exact_mod_cast (by omega : 0 < p)
  have hpne : p ≠ 0 := by omega
  have hm0 : 0 ≤ lpMoment p F := by
    unfold lpMoment uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => pow_nonneg (abs_nonneg _) _))
      (Nat.cast_nonneg _)
  have hroot := Real.rpow_le_rpow hm0 hmoment (by positivity : 0 ≤ 1 / (p : Real))
  have hcoef : 500 * i ^ 2 * p ^ 2 = (500 * i ^ 2 * p) * p := by ring
  have hdensity : (delta ^ (p - 2)) ^ (1 / (p : Real)) =
      delta ^ (((p : Real) - 2) / (p : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdelta]
    congr 1
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    push_cast
    ring
  change lpNorm p F ≤ _ at hroot
  rw [Real.mul_rpow (by positivity) (pow_nonneg hdelta _), hcoef, pow_mul,
    one_div, Real.pow_rpow_inv_natCast (by positivity) hpne, ← one_div, hdensity] at hroot
  exact hroot

/-- Full original exact-budget Boolean HC46, including eta>1 and eta=0. -/
theorem original_HC46_exact : HC46ExactContract := by
  intro n d h r i p eta hEven b hPR hi hp4 hdyadic
  by_cases hi0 : i = 0
  · subst i
    exact hc46_rank_zero_exact hEven b hPR hp4 hdyadic
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
end PvNP.RealizableHardness.ActualBinaryMatrixHC46OriginalExactInhabitant
