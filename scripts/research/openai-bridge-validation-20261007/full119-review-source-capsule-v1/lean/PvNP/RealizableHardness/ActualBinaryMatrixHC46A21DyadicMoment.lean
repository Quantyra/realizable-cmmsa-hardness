import PvNP.RealizableHardness.ActualBinaryMatrixHC46A20SquareGlobalness
import PvNP.RealizableHardness.ActualBinaryMatrixHC46A12InfluenceBound

/-! Original arbitrary-complex dyadic A21. The square-globalness parameter
is derived by A20; induction is simultaneous over all dimensions, degrees
and globalness parameters. Natural powers include zero parameters/degrees. -/
namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A21DyadicMoment
open ActualBinaryMatrixHC46A20SquareGlobalness
open ActualBinaryMatrixHC46A12InfluenceBound
open ActualTypedABFullA16Assembly
open ActualBinaryMatrixHC46A18SourceGlobal
open ActualFiniteDegreeFourierReconstruction
open BinaryMatrixFourier BinaryMatrixComplexA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section

def a21Exponent (p : Nat) : Nat := 200 * p ^ 2 - 100 * p

theorem a21_exponent_le (p : Nat) : a21Exponent p ≤ 200 * p ^ 2 :=
  Nat.sub_le _ _

theorem a21_exponent_recurrence {q : Nat} (hq : 4 ≤ q) (heven : 2 * (q / 2) = q) :
    4 * a21Exponent q + 196 * (q / 2 - 1) + 114 ≤ a21Exponent (2 * q) := by
  have hqsub : 100 * q ≤ 200 * q ^ 2 := by nlinarith
  have h2qsub : 100 * (2 * q) ≤ 200 * (2 * q) ^ 2 := by nlinarith
  have hqexp : a21Exponent q + 100 * q = 200 * q ^ 2 :=
    Nat.sub_add_cancel hqsub
  have h2qexp : a21Exponent (2 * q) + 100 * (2 * q) = 200 * (2 * q) ^ 2 :=
    Nat.sub_add_cancel h2qsub
  have hhalf : 2 ≤ q / 2 := by omega
  have hsub : q / 2 - 1 + 1 = q / 2 := Nat.sub_add_cancel (by omega)
  nlinarith

theorem a21_density_recurrence {q : Nat} (hq : 4 ≤ q) (heven : 2 * (q / 2) = q) :
    1 + 2 * (q / 2 - 1) = (2 * q) / 2 - 1 := by omega

theorem a21_moment_even {n d : Nat} (f : BinaryMatrix n d → Complex) (q : Nat) :
    lpMoment (2 * q) (fun M => ‖f M‖) =
      uniformMean (fun M => Complex.normSq (f M) ^ q) := by
  unfold lpMoment
  congr 1
  funext M
  rw [abs_of_nonneg (norm_nonneg _), Complex.normSq_eq_norm_sq, ← pow_mul]

theorem a21_square_moment {n d : Nat} (f : BinaryMatrix n d → Complex) (q : Nat) :
    lpMoment q (fun M => ‖f M * f M‖) = lpMoment (2 * q) (fun M => ‖f M‖) := by
  unfold lpMoment
  congr 1
  funext M
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), norm_mul,
    ← pow_two, ← pow_mul]

theorem a21_square_second {n d : Nat} (f : BinaryMatrix n d → Complex) :
    uniformMean (fun M => Complex.normSq (f M * f M)) =
      uniformMean (fun M => Complex.normSq (f M) ^ 2) := by
  congr 1
  funext M
  rw [Complex.normSq_mul, pow_two]

theorem a21_second_nonneg {n d : Nat} (f : BinaryMatrix n d → Complex) :
    0 ≤ uniformMean (fun M => Complex.normSq (f M)) := by
  unfold uniformMean
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
    (Nat.cast_nonneg _)

/-- The dyadic recursion is proved with a stronger envelope. At each step
the induction statement quantifies all matrix spaces, degree and parameter. -/
theorem a21_dyadic_strong (k : Nat) :
    ∀ {n d D : Nat} {eps : Real} (f : BinaryMatrix n d → Complex),
      ComplexFourierSupportedThrough D f → UpToActualNormSqGlobal D eps f →
      lpMoment (2 ^ (k + 1)) (fun M => ‖f M‖) ≤
        (2 : Real) ^ (a21Exponent (2 ^ (k + 1)) * D ^ 2) *
          uniformMean (fun M => Complex.normSq (f M)) * eps ^ (2 ^ (k + 1) / 2 - 1) := by
  induction k with
  | zero =>
      intro n d D eps f _hsupport _hglobal
      have hfactor : (1 : Real) ≤ (2 : Real) ^ (a21Exponent 2 * D ^ 2) :=
        one_le_pow₀ (by norm_num)
      have hsecond := a21_second_nonneg f
      have hmoment : lpMoment 2 (fun M => ‖f M‖) =
          uniformMean (fun M => Complex.normSq (f M)) := by
        simpa only [Nat.mul_one, pow_one] using a21_moment_even f 1
      change lpMoment 2 (fun M => ‖f M‖) ≤
        (2 : Real) ^ (a21Exponent 2 * D ^ 2) *
          uniformMean (fun M => Complex.normSq (f M)) * eps ^ 0
      rw [hmoment, pow_zero, mul_one]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hsecond
  | succ k ih =>
      intro n d D eps f hsupport hglobal
      have heps : 0 ≤ eps := filteredCarrierFunction_parameter_nonneg f hglobal
      by_cases hk : k = 0
      · subst k
        have hA19 := manuscript_A19_actual f hsupport hglobal
        have hpow : (2 : Real) ^ (114 * D ^ 2) ≤
            (2 : Real) ^ (a21Exponent 4 * D ^ 2) := by
          apply pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2)
          have h114 : 114 ≤ a21Exponent 4 := by norm_num [a21Exponent]
          exact Nat.mul_le_mul_right (D ^ 2) h114
        have hnonneg : 0 ≤ eps * uniformMean (fun M => Complex.normSq (f M)) :=
          mul_nonneg heps (a21_second_nonneg f)
        calc
          lpMoment (2 ^ (0 + 1 + 1)) (fun M => ‖f M‖) =
              uniformMean (fun M => Complex.normSq (f M) ^ 2) := by
            simpa using a21_moment_even f 2
          _ ≤ (2 : Real) ^ (114 * D ^ 2) * eps *
              uniformMean (fun M => Complex.normSq (f M)) := hA19
          _ ≤ (2 : Real) ^ (a21Exponent 4 * D ^ 2) * eps *
              uniformMean (fun M => Complex.normSq (f M)) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpow hnonneg
          _ = _ := by norm_num; ring
      · let q := 2 ^ (k + 1)
        have hq : 4 ≤ q := by
          change 2 ^ 2 ≤ 2 ^ (k + 1)
          apply Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
          omega
        have hqhalf : q / 2 = 2 ^ k := by
          dsimp [q]
          rw [pow_succ, Nat.mul_div_left _ (by decide : 0 < (2 : Nat))]
        have heven : 2 * (q / 2) = q := by
          rw [hqhalf]
          simp only [q, pow_succ, Nat.mul_comm]
        have htarget : 2 ^ (k + 1 + 1) = 2 * q := by
          simp only [q, pow_succ, Nat.mul_comm]
        let g : BinaryMatrix n d → Complex := fun M => f M * f M
        let eta : Real := (2 : Real) ^ (196 * D ^ 2) * eps ^ 2
        have hgSupport : ComplexFourierSupportedThrough (2 * D) g :=
          manuscript_A20_square_supportedThrough f hsupport
        have hgGlobal : UpToActualNormSqGlobal (2 * D) eta g :=
          manuscript_A20_actual f hsupport hglobal
        have hIH := ih g hgSupport hgGlobal
        have hsecond : uniformMean (fun M => Complex.normSq (g M)) ≤
            (2 : Real) ^ (114 * D ^ 2) * eps *
              uniformMean (fun M => Complex.normSq (f M)) := by
          change uniformMean (fun M => Complex.normSq (f M * f M)) ≤ _
          rw [a21_square_second]
          exact manuscript_A19_actual f hsupport hglobal
        have houter : 0 ≤ (2 : Real) ^ (a21Exponent q * (2 * D) ^ 2) := by positivity
        have heta : 0 ≤ eta ^ (q / 2 - 1) := by dsimp [eta]; positivity
        have hdensity := a21_density_recurrence hq heven
        have hexponent := a21_exponent_recurrence hq heven
        have htotal : a21Exponent q * (2 * D) ^ 2 + 114 * D ^ 2 +
            (196 * D ^ 2) * (q / 2 - 1) ≤ a21Exponent (2 * q) * D ^ 2 := by
          have h := Nat.mul_le_mul_right (D ^ 2) hexponent
          nlinarith
        have halgebra :
            (2 : Real) ^ (a21Exponent q * (2 * D) ^ 2) *
              ((2 : Real) ^ (114 * D ^ 2) * eps *
                uniformMean (fun M => Complex.normSq (f M))) * eta ^ (q / 2 - 1) =
            (2 : Real) ^ (a21Exponent q * (2 * D) ^ 2 + 114 * D ^ 2 +
              (196 * D ^ 2) * (q / 2 - 1)) *
                uniformMean (fun M => Complex.normSq (f M)) * eps ^ ((2 * q) / 2 - 1) := by
          dsimp [eta]
          rw [mul_pow ((2 : Real) ^ (196 * D ^ 2)) (eps ^ 2) (q / 2 - 1),
            ← pow_mul, ← pow_mul]
          rw [← hdensity]
          simp only [pow_add, pow_one]
          ring
        rw [htarget]
        calc
          lpMoment (2 * q) (fun M => ‖f M‖) = lpMoment q (fun M => ‖g M‖) :=
            (a21_square_moment f q).symm
          _ ≤ (2 : Real) ^ (a21Exponent q * (2 * D) ^ 2) *
              uniformMean (fun M => Complex.normSq (g M)) * eta ^ (q / 2 - 1) := hIH
          _ ≤ (2 : Real) ^ (a21Exponent q * (2 * D) ^ 2) *
              ((2 : Real) ^ (114 * D ^ 2) * eps *
                uniformMean (fun M => Complex.normSq (f M))) * eta ^ (q / 2 - 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsecond houter) heta
          _ = _ := halgebra
          _ ≤ (2 : Real) ^ (a21Exponent (2 * q) * D ^ 2) *
              uniformMean (fun M => Complex.normSq (f M)) * eps ^ ((2 * q) / 2 - 1) := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg heps _)
            apply mul_le_mul_of_nonneg_right _ (a21_second_nonneg f)
            exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) htotal

/-- Original A21 for every complex source and dyadic p≥2. There is no
positive-degree, positive-parameter, Boolean or square-globalness guard. -/
theorem manuscript_A21_actual {n d D p : Nat} {eps : Real}
    (f : BinaryMatrix n d → Complex) (hsupport : ComplexFourierSupportedThrough D f)
    (hglobal : UpToActualNormSqGlobal D eps f)
    (hp2 : 2 ≤ p) (hdyadic : ∃ k : Nat, p = 2 ^ k) :
    lpMoment p (fun M => ‖f M‖) ≤
      (2 : Real) ^ (200 * D ^ 2 * p ^ 2) *
        uniformMean (fun M => Complex.normSq (f M)) * eps ^ (p / 2 - 1) := by
  obtain ⟨k, rfl⟩ := hdyadic
  obtain ⟨j, rfl⟩ : ∃ j : Nat, k = j + 1 := by
    have hk : k ≠ 0 := by intro hz; simp [hz] at hp2
    exact ⟨k - 1, by omega⟩
  have hstrong := a21_dyadic_strong j f hsupport hglobal
  have heps : 0 ≤ eps := filteredCarrierFunction_parameter_nonneg f hglobal
  have hexp : a21Exponent (2 ^ (j + 1)) * D ^ 2 ≤
      200 * D ^ 2 * (2 ^ (j + 1)) ^ 2 := by
    have h := Nat.mul_le_mul_right (D ^ 2) (a21_exponent_le (2 ^ (j + 1)))
    nlinarith
  exact hstrong.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hexp)
      (a21_second_nonneg f)) (pow_nonneg heps _))

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A21DyadicMoment
