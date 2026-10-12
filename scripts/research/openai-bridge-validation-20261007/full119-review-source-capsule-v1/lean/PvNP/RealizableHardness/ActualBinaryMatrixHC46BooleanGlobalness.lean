import PvNP.RealizableHardness.ActualBinaryMatrixHC46
import PvNP.RealizableHardness.BinaryMatrixComplexA15
import PvNP.RealizableHardness.BinaryMatrixComplexA14

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46BooleanGlobalness

open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualBinaryMatrixHC46
open PvNP.RealizableHardness.BinaryMatrixComplexA15
open PvNP.RealizableHardness.BinaryMatrixComplexA14
open PvNP.RealizableHardness.BinaryMatrixHybridSelector
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complex embedding of the manuscript's Boolean indicator. -/
def booleanIndicatorComplex {n d : Nat} (b : BinaryMatrix n d → Bool) :
    BinaryMatrix n d → Complex := fun M => (indicator b M : Complex)

/-- The complex Fourier rank projection of the Boolean indicator is exactly
the real manuscript rank projection embedded back into `Complex`. -/
theorem complexRankProjection_boolean_eq {n d j : Nat}
    (b : BinaryMatrix n d → Bool) (M : BinaryMatrix n d) :
    complexRankProjection j (booleanIndicatorComplex b) M =
      (rankProjection j (indicator b) M : Complex) := by
  apply Complex.ext
  · rw [complexRankProjection_re]
    simp [booleanIndicatorComplex]
  · rw [complexRankProjection_im]
    simp [booleanIndicatorComplex, rankProjection, fourierCoeff, uniformMean]

/-- Squared complex magnitude agrees pointwise with the real squared
projection used by HC46. -/
theorem complexRankProjection_boolean_normSq {n d j : Nat}
    (b : BinaryMatrix n d → Bool) (M : BinaryMatrix n d) :
    Complex.normSq (complexRankProjection j (booleanIndicatorComplex b) M) =
      (rankProjection j (indicator b) M) ^ 2 := by
  rw [complexRankProjection_boolean_eq]
  simp [Complex.normSq_ofReal]
  ring

/-- Exact nominal-budget Boolean pseudorandomness gives the corresponding
complex squared-norm bound on every nonempty or empty raw affine fibre.  The
nonempty case is the actual density statement; the empty case uses the
nonnegativity of the ambient Boolean mean, which also implies `eta ≥ 0`. -/
theorem exactPR_to_raw_normSqGlobal {n d r : Nat} {eta : Real}
    (b : BinaryMatrix n d → Bool)
    (hPR : PseudorandomExact r eta b) :
    UpToRawNormSqGlobal r eta (booleanIndicatorComplex b) := by
  have heta0 : 0 ≤ eta :=
    (uniformMean_indicator_nonneg b).trans (boolean_mean_le_of_exact b hPR)
  intro R hR
  by_cases hne : R.fibre.Nonempty
  · have hden := pseudorandom_atMost_of_exact hPR R hR hne
    have hsum :
        (∑ M ∈ R.fibre, Complex.normSq (booleanIndicatorComplex b M)) =
          ((R.fibre.filter (fun M => b M = true)).card : Real) := by
      calc
        (∑ M ∈ R.fibre, Complex.normSq (booleanIndicatorComplex b M)) =
            ∑ M ∈ R.fibre, if b M = true then (1 : Real) else 0 := by
              apply Finset.sum_congr rfl
              intro M hM
              by_cases hb : b M = true <;>
                simp [booleanIndicatorComplex, indicator, hb]
        _ = ∑ M ∈ R.fibre.filter (fun M => b M = true), (1 : Real) := by
              rw [← Finset.sum_filter]
        _ = ((R.fibre.filter (fun M => b M = true)).card : Real) := by
              simp
    have henergy :
        fibreEnergy R.fibre (booleanIndicatorComplex b) = R.density b := by
      unfold fibreEnergy AffineRestriction.density
      rw [hsum]
    change fibreEnergy R.fibre (booleanIndicatorComplex b) ≤ eta
    rw [henergy]
    exact hden
  · have hEmpty : R.fibre = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [fibreEnergy, hEmpty, heta0]

/-- The exact Boolean premise also gives the actual-affine form consumed by
the A15 globalness step. -/
theorem exactPR_to_actual_normSqGlobal {n d r : Nat} {eta : Real}
    (b : BinaryMatrix n d → Bool)
    (hPR : PseudorandomExact r eta b) :
    UpToActualNormSqGlobal r eta (booleanIndicatorComplex b) := by
  apply raw_implies_actual
  exact exactPR_to_raw_normSqGlobal b hPR

/-- One genuine A15 line step from the exact Boolean premise.  The error
constant is the source's stated `4 * 2^(4*(k+1))` loss; this does not yet
iterate the dyadic moment argument needed for HC46. -/
theorem exactPR_to_actual_A15_fixedLine {n d k : Nat} {eta : Real}
    (t : Fin n → ZMod 2)
    (b : BinaryMatrix n (d + 1) → Bool)
    (hPR : PseudorandomExact (k + 1) eta b) :
    UpToActualNormSqGlobal k
      (4 * (2 : Real) ^ (4 * (k + 1)) * eta)
      (fun M => complexLineP k (booleanIndicatorComplex b)
        (BinaryMatrixFirstDerivative.rawLastColumn M t)) := by
  have heta0 : 0 ≤ eta :=
    (uniformMean_indicator_nonneg b).trans (boolean_mean_le_of_exact b hPR)
  exact actualGlobal_A15_complex_fixedLine t (booleanIndicatorComplex b)
    heta0 (exactPR_to_actual_normSqGlobal b hPR)

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46BooleanGlobalness
