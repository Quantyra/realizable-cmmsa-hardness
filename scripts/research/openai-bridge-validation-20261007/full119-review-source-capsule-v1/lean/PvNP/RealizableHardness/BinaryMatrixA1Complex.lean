import PvNP.RealizableHardness.BinaryMatrixA1Composition
import Mathlib.Basic.Complex.BigOperators

namespace PvNP.RealizableHardness.BinaryMatrixA1Complex

open BinaryMatrixFourier BinaryMatrixA1Composition BinaryMatrixA1TypedFourier
open BinaryMatrixNestedSelectorA1
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

private noncomputable instance carrierFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype ((V d ⧸ A) →ₗ[F] B) := by
  classical
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

def complexFourierCoeff {n d : ℕ} (f : BinaryMatrix n d → ℂ)
    (Y : BinaryMatrix n d) : ℂ :=
  (∑ M : BinaryMatrix n d, f M * (character Y M : ℂ)) /
    (Fintype.card (BinaryMatrix n d) : ℂ)

theorem complexFourierCoeff_re {n d : ℕ}
    (f : BinaryMatrix n d → ℂ) (Y : BinaryMatrix n d) :
    (complexFourierCoeff f Y).re = fourierCoeff (fun M => (f M).re) Y := by
  simp [complexFourierCoeff, fourierCoeff, uniformMean,
    Complex.mul_re]

theorem complexFourierCoeff_im {n d : ℕ}
    (f : BinaryMatrix n d → ℂ) (Y : BinaryMatrix n d) :
    (complexFourierCoeff f Y).im = fourierCoeff (fun M => (f M).im) Y := by
  simp [complexFourierCoeff, fourierCoeff, uniformMean,
    Complex.mul_im]

def complexCarrierFourierCoeff {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] (V d ⧸ A)) : ℂ :=
  (∑ M : (V d ⧸ A) →ₗ[F] B,
    g M * (BinaryMatrixA1Phase.traceCharacter Y M : ℂ)) /
      (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℂ)

theorem complexCarrierFourierCoeff_re {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    (complexCarrierFourierCoeff A B g Y).re =
      carrierFourierCoeff A B (fun M => (g M).re) Y := by
  simp [complexCarrierFourierCoeff, carrierFourierCoeff, carrierMean,
    Complex.mul_re]

theorem complexCarrierFourierCoeff_im {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (g : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    (complexCarrierFourierCoeff A B g Y).im =
      carrierFourierCoeff A B (fun M => (g M).im) Y := by
  simp [complexCarrierFourierCoeff, carrierFourierCoeff, carrierMean,
    Complex.mul_im]

def complexAmbientHybridFilter {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → ℂ) (M : BinaryMatrix n d) : ℂ :=
  ∑ Y : BinaryMatrix n d,
    if Selected A B Y.transpose.toLin' then
      complexFourierCoeff f Y * (character Y M : ℂ) else 0

theorem complexAmbientHybridFilter_re {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → ℂ) (M : BinaryMatrix n d) :
    (complexAmbientHybridFilter A B f M).re =
      ambientHybridFilter A B (fun X => (f X).re) M := by
  unfold complexAmbientHybridFilter ambientHybridFilter
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases h : Selected A B Y.transpose.toLin' <;>
    simp [h, complexFourierCoeff_re, Complex.mul_re]

theorem complexAmbientHybridFilter_im {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : BinaryMatrix n d → ℂ) (M : BinaryMatrix n d) :
    (complexAmbientHybridFilter A B f M).im =
      ambientHybridFilter A B (fun X => (f X).im) M := by
  unfold complexAmbientHybridFilter ambientHybridFilter
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases h : Selected A B Y.transpose.toLin' <;>
    simp [h, complexFourierCoeff_im, Complex.mul_im]

def complexCarrierHybridFilter {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℂ)
    (M : (V d ⧸ A₂) →ₗ[F] B₂) : ℂ :=
  ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
    if Selected A₁₂ B₁₂ Z then
      complexCarrierFourierCoeff A₂ B₂ g Z *
        (BinaryMatrixA1Phase.traceCharacter Z M : ℂ) else 0

theorem complexCarrierHybridFilter_re {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℂ)
    (M : (V d ⧸ A₂) →ₗ[F] B₂) :
    (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g M).re =
      carrierHybridFilter A₂ B₂ A₁₂ B₁₂ (fun X => (g X).re) M := by
  unfold complexCarrierHybridFilter carrierHybridFilter
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro Z _
  by_cases h : Selected A₁₂ B₁₂ Z <;>
    simp [h, complexCarrierFourierCoeff_re, Complex.mul_re]

theorem complexCarrierHybridFilter_im {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℂ)
    (M : (V d ⧸ A₂) →ₗ[F] B₂) :
    (complexCarrierHybridFilter A₂ B₂ A₁₂ B₁₂ g M).im =
      carrierHybridFilter A₂ B₂ A₁₂ B₁₂ (fun X => (g X).im) M := by
  unfold complexCarrierHybridFilter carrierHybridFilter
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro Z _
  by_cases h : Selected A₁₂ B₁₂ Z <;>
    simp [h, complexCarrierFourierCoeff_im, Complex.mul_im]

def complexAmbientAffineRestrict {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → ℂ)
    (N : (V d ⧸ A) →ₗ[F] B) : ℂ :=
  f (LinearMap.toMatrix' (T + B.subtype.comp (N.comp A.mkQ)))

def complexCarrierAffineRestrict {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℂ)
    (N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂) : ℂ :=
  g (S + B₁₂.subtype.comp (N.comp A₁₂.mkQ))

/-- Manuscript (A1) for complex-valued functions, with direct complex
Fourier coefficients and exact canonical quotient/inclusion carriers. -/
theorem manuscript_A1_complex {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (f : BinaryMatrix n d → ℂ)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype)) :
    complexCarrierAffineRestrict A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype) S
      (complexCarrierHybridFilter A₂ B₂ (A₁.map A₂.mkQ) (B₁.comap B₂.subtype)
        (fun M => complexAmbientAffineRestrict A₂ B₂ T
          (complexAmbientHybridFilter A₂ B₂ f) M)) N =
      complexAmbientAffineRestrict A₁ B₁
        (T + B₂.subtype.comp (S.comp A₂.mkQ))
        (complexAmbientHybridFilter A₁ B₁ f)
        (BinaryMatrixA1NestedCarrier.nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) := by
  apply Complex.ext
  · unfold complexCarrierAffineRestrict complexAmbientAffineRestrict
    rw [complexCarrierHybridFilter_re]
    simp_rw [complexAmbientHybridFilter_re]
    exact manuscript_A1_restrict_filter A₂ A₁ B₁ B₂ hA hB T S
      (fun M => (f M).re) N
  · unfold complexCarrierAffineRestrict complexAmbientAffineRestrict
    rw [complexCarrierHybridFilter_im]
    simp_rw [complexAmbientHybridFilter_im]
    exact manuscript_A1_restrict_filter A₂ A₁ B₁ B₂ hA hB T S
      (fun M => (f M).im) N

end
end PvNP.RealizableHardness.BinaryMatrixA1Complex
