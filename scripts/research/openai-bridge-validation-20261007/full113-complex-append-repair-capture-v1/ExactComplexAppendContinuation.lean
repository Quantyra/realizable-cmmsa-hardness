import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic
import PvNP.RealizableHardness.BinaryMatrixFourier
import PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
import PvNP.RealizableHardness.ActualFiniteFrameProductDuality
import PvNP.RealizableHardness.ExactAppendOperatorContracts
import PvNP.RealizableHardness.ExactPhiEigenrelation

/-!
Literal complex extension of the finite binary Fourier objects and actual
unconditional append. Every complex mean below is the normalized finite sum
it names. The exact normSq energy theorem reduces to the qualified real
Full107 product-energy identity by taking real and imaginary parts separately.
The Phi eigenrelation depends explicitly on the frozen, still uncompiled real
ExactPhiEigenrelation offer. This source offer has not been compiled.
-/

namespace PvNP.RealizableHardness.ExactComplexAppendContinuation

open scoped BigOperators
open PvNP.RealizableHardness.BinaryMatrixFourier
open PvNP.RealizableHardness.ActualFixedFunctionalAppendOperator
open PvNP.RealizableHardness.ActualFiniteFrameProductDuality
open PvNP.RealizableHardness.ExactAppendOperatorContracts
open PvNP.RealizableHardness.ExactPhiEigenrelation

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Fintype.ofFinite

/-- Literal normalized complex mean over a finite carrier. The real cast in
the denominator is the cardinality interpreted in the complex field. -/
def complexFiniteMean {α : Type*} [Fintype α] (f : α → Complex) : Complex :=
  (∑ x, f x) / (Fintype.card α : Real)

/-- The real part commutes with the literal normalized finite mean, including
the totalized zero-cardinality case. -/
theorem complexFiniteMean_re {α : Type*} [Fintype α] (f : α → Complex) :
    (complexFiniteMean f).re =
      (∑ x, (f x).re) / (Fintype.card α : Real) := by
  unfold complexFiniteMean
  rw [Complex.div_ofReal_re, Complex.re_sum]

/-- The imaginary part commutes with the literal normalized finite mean,
including the totalized zero-cardinality case. -/
theorem complexFiniteMean_im {α : Type*} [Fintype α] (f : α → Complex) :
    (complexFiniteMean f).im =
      (∑ x, (f x).im) / (Fintype.card α : Real) := by
  unfold complexFiniteMean
  rw [Complex.div_ofReal_im, Complex.im_sum]

/-- Literal complex normalized Fourier coefficient. The real binary character
is included in the finite summand as its complex cast. -/
def complexFourierCoeff {n d : Nat} (F : BinaryMatrix n d → Complex)
    (Y : BinaryMatrix n d) : Complex :=
  complexFiniteMean (fun M => F M * (character Y M : Complex))

theorem complexFourierCoeff_re {n d : Nat}
    (F : BinaryMatrix n d → Complex) (Y : BinaryMatrix n d) :
    (complexFourierCoeff F Y).re =
      fourierCoeff (fun M => (F M).re) Y := by
  unfold complexFourierCoeff
  rw [complexFiniteMean_re]
  unfold fourierCoeff uniformMean
  congr 1
  apply Finset.sum_congr rfl
  intro M hM
  simp [Complex.mul_re]

theorem complexFourierCoeff_im {n d : Nat}
    (F : BinaryMatrix n d → Complex) (Y : BinaryMatrix n d) :
    (complexFourierCoeff F Y).im =
      fourierCoeff (fun M => (F M).im) Y := by
  unfold complexFourierCoeff
  rw [complexFiniteMean_im]
  unfold fourierCoeff uniformMean
  congr 1
  apply Finset.sum_congr rfl
  intro M hM
  simp [Complex.mul_im]

/-- Literal complex rank-i Fourier projection. -/
def complexRankProjection {n d : Nat} (i : Nat)
    (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) : Complex :=
  ∑ Y ∈ (Finset.univ : Finset (BinaryMatrix n d)).filter
      (fun Y => Y.rank = i),
    complexFourierCoeff F Y * (character Y M : Complex)

theorem complexRankProjection_re {n d i : Nat}
    (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) :
    (complexRankProjection i F M).re =
      rankProjection i (fun X => (F X).re) M := by
  unfold complexRankProjection rankProjection
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro Y hY
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    complexFourierCoeff_re, mul_zero, sub_zero]

theorem complexRankProjection_im {n d i : Nat}
    (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) :
    (complexRankProjection i F M).im =
      rankProjection i (fun X => (F X).im) M := by
  unfold complexRankProjection rankProjection
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro Y hY
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    complexFourierCoeff_im, mul_zero, zero_add]

/-- Literal complex form of the actual unconditional append-column mean. -/
def complexAppendAverage {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Complex) (M : BinaryMatrix n c) : Complex :=
  complexFiniteMean (fun B : BinaryMatrix n s =>
    F (appendBinaryMatrix M B))

theorem complexAppendAverage_re {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Complex) (M : BinaryMatrix n c) :
    (complexAppendAverage F M).re =
      appendAverage (fun X => (F X).re) M := by
  unfold complexAppendAverage appendAverage
  rw [complexFiniteMean_re]
  unfold uniformMean
  rfl

theorem complexAppendAverage_im {n c s : Nat}
    (F : BinaryMatrix n (c + s) → Complex) (M : BinaryMatrix n c) :
    (complexAppendAverage F M).im =
      appendAverage (fun X => (F X).im) M := by
  unfold complexAppendAverage appendAverage
  rw [complexFiniteMean_im]
  unfold uniformMean
  rfl

/-- Paired-inverse right invariance of a complex function is exactly paired-
inverse right invariance of its two real components. -/
theorem complexRightInvariant_iff_components {n d : Nat}
    (F : BinaryMatrix n d → Complex) :
    (∀ (M : BinaryMatrix n d) (U V : BinaryMatrix d d),
      U * V = 1 → V * U = 1 → F (M * U) = F M) ↔
      RightInvariant (fun M => (F M).re) ∧
        RightInvariant (fun M => (F M).im) := by
  constructor
  · intro h
    constructor <;> intro M U V hUV hVU
    · exact congrArg Complex.re (h M U V hUV hVU)
    · exact congrArg Complex.im (h M U V hUV hVU)
  · rintro ⟨hRe, hIm⟩ M U V hUV hVU
    exact Complex.ext (hRe M U V hUV hVU) (hIm M U V hUV hVU)

/-- Conjugation-free squared magnitude is the sum of the two real component
energies under the same normalized finite mean. -/
theorem uniformMean_normSq_components {n d : Nat}
    (F : BinaryMatrix n d → Complex) :
    uniformMean (fun M => Complex.normSq (F M)) =
      uniformMean (fun M => (F M).re ^ 2) +
        uniformMean (fun M => (F M).im ^ 2) := by
  unfold uniformMean
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro M hM
  change Complex.normSq (F M) = (F M).re ^ 2 + (F M).im ^ 2
  rw [Complex.normSq_apply]
  ring

private theorem complexAppendRankProjection_re {n c s i : Nat}
    (F : BinaryMatrix n (c + s) → Complex) (M : BinaryMatrix n c) :
    (complexAppendAverage (complexRankProjection i F) M).re =
      appendAverage (rankProjection i (fun X => (F X).re)) M := by
  simp_rw [complexAppendAverage_re, complexRankProjection_re]

private theorem complexAppendRankProjection_im {n c s i : Nat}
    (F : BinaryMatrix n (c + s) → Complex) (M : BinaryMatrix n c) :
    (complexAppendAverage (complexRankProjection i F) M).im =
      appendAverage (rankProjection i (fun X => (F X).im)) M := by
  simp_rw [complexAppendAverage_im, complexRankProjection_im]

private theorem complexRankProjection_energy_components {n d i : Nat}
    (F : BinaryMatrix n d → Complex) :
    uniformMean (fun M =>
      Complex.normSq (complexRankProjection i F M)) =
      uniformMean (fun M =>
        (rankProjection i (fun X => (F X).re) M) ^ 2) +
      uniformMean (fun M =>
        (rankProjection i (fun X => (F X).im) M) ^ 2) := by
  have h := uniformMean_normSq_components
    (F := fun M => complexRankProjection i F M)
  simpa [complexRankProjection_re, complexRankProjection_im] using h

/-- Exact complex normSq product-energy identity for the literal append
operator. It is derived by applying the qualified real Full107 product-energy
theorem to real and imaginary parts and adding the two equalities. -/
theorem complexAppend_rankProjection_energy_eq_product
    {n c s i : Nat} (hi : i ≤ c + s)
    (F : BinaryMatrix n (c + s) → Complex)
    (basisInv : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 → F (M * U) = F M) :
    uniformMean (fun M : BinaryMatrix n c =>
      Complex.normSq (complexAppendAverage (complexRankProjection i F) M)) =
      (∏ j : Fin s,
        (((2 : Real) ^ (c + s - i) - (2 : Real) ^ j.val) /
          ((2 : Real) ^ (c + s) - (2 : Real) ^ j.val))) *
      uniformMean (fun W : BinaryMatrix n (c + s) =>
        Complex.normSq (complexRankProjection i F W)) := by
  have hInvRe : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 →
        (F (M * U)).re = (F M).re := by
    intro M U V hUV hVU
    exact congrArg Complex.re (basisInv M U V hUV hVU)
  have hInvIm : ∀ (M : BinaryMatrix n (c + s))
      (U V : BinaryMatrix (c + s) (c + s)),
      U * V = 1 → V * U = 1 →
        (F (M * U)).im = (F M).im := by
    intro M U V hUV hVU
    exact congrArg Complex.im (basisInv M U V hUV hVU)
  have hRe := append_rank_projection_energy_eq_product
    hi (fun X => (F X).re) hInvRe
  have hIm := append_rank_projection_energy_eq_product
    hi (fun X => (F X).im) hInvIm
  have hLeft := uniformMean_normSq_components
    (F := fun M => complexAppendAverage (complexRankProjection i F) M)
  have hRight := complexRankProjection_energy_components (i := i) F
  rw [hLeft, hRight]
  simp_rw [complexAppendRankProjection_re, complexAppendRankProjection_im]
  rw [hRe, hIm]
  ring

/-- Literal complex Phi average over independent unrestricted B and full-row
frame C, using the source-shaped product carrier from the operator contract. -/
def complexPhiAverage {n d s : Nat}
    (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) : Complex :=
  complexFiniteMean (fun p : BinaryMatrix n s × FullRowFrame s d =>
    F (M + p.1 * p.2.1))

theorem complexPhiAverage_re {n d s : Nat}
    (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) :
    (complexPhiAverage (s := s) F M).re =
      phiAverage (s := s) (fun X => (F X).re) M := by
  unfold complexPhiAverage
  rw [complexFiniteMean_re]
  unfold phiAverage
  rfl

theorem complexPhiAverage_im {n d s : Nat}
    (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) :
    (complexPhiAverage (s := s) F M).im =
      phiAverage (s := s) (fun X => (F X).im) M := by
  unfold complexPhiAverage
  rw [complexFiniteMean_im]
  unfold phiAverage
  rfl

/-- Literal complex Phi has the same pointwise rank-projection eigenrelation
as the frozen real arbitrary-F theorem. This depends explicitly on that
uncompiled real source offer and assumes only the nonempty-frame guard s≤d. -/
theorem complexPhi_rankProjection_eigen {n d s i : Nat}
    (hs : s ≤ d) (F : BinaryMatrix n d → Complex) (M : BinaryMatrix n d) :
    complexPhiAverage (s := s) (complexRankProjection i F) M =
      (∏ j : Fin s,
        (((2 : Real) ^ (d - i) - (2 : Real) ^ j.val) /
          ((2 : Real) ^ d - (2 : Real) ^ j.val)) : Real) *
        complexRankProjection i F M := by
  apply Complex.ext
  · rw [complexPhiAverage_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simp_rw [complexRankProjection_re]
    exact phiAverage_rankProjection_eigen (s := s) hs
      (fun X => (F X).re) M
  · rw [complexPhiAverage_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    simp_rw [complexRankProjection_im]
    exact phiAverage_rankProjection_eigen (s := s) hs
      (fun X => (F X).im) M

end
end PvNP.RealizableHardness.ExactComplexAppendContinuation
