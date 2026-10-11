import PvNP.RealizableHardness.BinaryMatrixRightOrbit

/-! Exact Fourier covariance for the all-matrix paired-inverse action.
This candidate supplies no orbit count or Spectral47 energy bound.
-/
namespace PvNP.RealizableHardness.BinaryMatrixRightFourierCovariance
open PvNP.RealizableHardness.BinaryMatrixFourier
set_option autoImplicit false
noncomputable section

/-- Right basis changes biject the complete matrix carrier. -/
def rightBasisEquiv {n d : Nat} (U V : BinaryMatrix d d)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    BinaryMatrix n d ≃ BinaryMatrix n d where
  toFun M := M * U
  invFun M := M * V
  left_inv M := by simp only [Matrix.mul_assoc, hUV, Matrix.mul_one]
  right_inv M := by simp only [Matrix.mul_assoc, hVU, Matrix.mul_one]

/-- The entrywise pairing moves a right action to its transpose. -/
theorem pairing_mul_right {n d : Nat}
    (Y M : BinaryMatrix n d) (U : BinaryMatrix d d) :
    pairing (Y * U) M = pairing Y (M * U.transpose) := by
  classical
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc
    (∑ j : Fin d, (∑ k : Fin d, Y i k * U k j) * M i j) =
        ∑ j : Fin d, ∑ k : Fin d, (Y i k * U k j) * M i j := by
          simp_rw [Finset.sum_mul]
    _ = ∑ k : Fin d, ∑ j : Fin d, (Y i k * U k j) * M i j :=
      Finset.sum_comm
    _ = ∑ k : Fin d, Y i k * (∑ j : Fin d, M i j * U k j) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Character covariance follows from the exact binary pairing. -/
theorem character_mul_right {n d : Nat}
    (Y M : BinaryMatrix n d) (U : BinaryMatrix d d) :
    character (Y * U) M = character Y (M * U.transpose) := by
  unfold character
  rw [pairing_mul_right]

/-- Uniform means reindex under a bijection of all matrices. -/
theorem uniformMean_comp_equiv {n d : Nat}
    (e : BinaryMatrix n d ≃ BinaryMatrix n d) (H : BinaryMatrix n d → Real) :
    uniformMean (fun M => H (e M)) = uniformMean H := by
  unfold uniformMean
  rw [Equiv.sum_comp e H]

/-- Full right-basis invariance transfers to Fourier coefficients. -/
theorem fourierCoeff_mul_right_of_basis_invariant {n d : Nat}
    (F : BinaryMatrix n d → Real)
    (hInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (Y : BinaryMatrix n d) (U V : BinaryMatrix d d)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    fourierCoeff F (Y * U) = fourierCoeff F Y := by
  classical
  have hUtVt : U.transpose * V.transpose = 1 := by
    have hh := congrArg Matrix.transpose hVU
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using hh
  have hVtUt : V.transpose * U.transpose = 1 := by
    have hh := congrArg Matrix.transpose hUV
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using hh
  let e : BinaryMatrix n d ≃ BinaryMatrix n d :=
    rightBasisEquiv U.transpose V.transpose hUtVt hVtUt
  unfold fourierCoeff
  calc
    uniformMean (fun M => F M * character (Y * U) M) =
        uniformMean (fun M => F (M * U.transpose) * character Y (M * U.transpose)) := by
      apply congrArg uniformMean
      funext M
      rw [character_mul_right, hInv M U.transpose V.transpose hUtVt hVtUt]
    _ = uniformMean (fun M => F M * character Y M) :=
      uniformMean_comp_equiv e (fun M => F M * character Y M)

/-- Fourier coefficients are constant on every image-space class. -/
theorem fourierCoeff_eq_of_same_range {n d : Nat}
    (F : BinaryMatrix n d → Real)
    (hInv : ∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M)
    (Y Z : BinaryMatrix n d)
    (h : LinearMap.range (Matrix.toLin' Y) = LinearMap.range (Matrix.toLin' Z)) :
    fourierCoeff F Y = fourierCoeff F Z := by
  apply BinaryMatrixRightOrbit.basis_invariant_eq_of_same_range (fourierCoeff F)
  · intro M U V hUV hVU
    exact fourierCoeff_mul_right_of_basis_invariant F hInv M U V hUV hVU
  · exact h

end
end PvNP.RealizableHardness.BinaryMatrixRightFourierCovariance
