import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
import PvNP.RealizableHardness.BinaryMatrixNestedSelectorA1

namespace PvNP.RealizableHardness.BinaryMatrixA1CoefficientTransfer

open BinaryMatrixA1Phase BinaryMatrixA1TypedFourier
  BinaryMatrixA1NestedCarrier BinaryMatrixNestedSelectorA1
open BinaryMatrixFourier
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def initialDerivative {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → ℝ)
    (N : (V d ⧸ A) →ₗ[F] B) : ℝ :=
  ∑ Y : BinaryMatrix n d,
    if Selected A B Y.transpose.toLin' then
      fourierCoeff f Y *
        traceCharacter Y.transpose.toLin'
          (T + B.subtype.comp (N.comp A.mkQ))
    else 0

def nextDerivative {n d : ℕ}
    (A₂ : Submodule F (V d)) (B₂ : Submodule F (W n))
    (A₁₂ : Submodule F (V d ⧸ A₂))
    (B₁₂ : Submodule F B₂)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (g : ((V d ⧸ A₂) →ₗ[F] B₂) → ℝ)
    (N : ((V d ⧸ A₂) ⧸ A₁₂) →ₗ[F] B₁₂) : ℝ :=
  ∑ Z : B₂ →ₗ[F] (V d ⧸ A₂),
    if Selected A₁₂ B₁₂ Z then
      carrierFourierCoeff A₂ B₂ g Z *
        traceCharacter Z
          (S + B₁₂.subtype.comp (N.comp A₁₂.mkQ))
    else 0

/-- Exact Fourier transfer through a finite sum of typed characters.
The indicator sum retains all collisions at the same induced frequency. -/
theorem carrierFourierCoeff_sum_characters {n d : ℕ} {ι : Type*}
    [Fintype ι] (A : Submodule F (V d)) (B : Submodule F (W n))
    (c : ι → ℝ) (φ : ι → (B →ₗ[F] (V d ⧸ A)))
    (Z : B →ₗ[F] (V d ⧸ A)) :
    carrierFourierCoeff A B
      (fun M => ∑ i : ι, c i * traceCharacter (φ i) M) Z =
      ∑ i : ι, if φ i = Z then c i else 0 := by
  unfold carrierFourierCoeff carrierMean
  have hcard : (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card ((V d ⧸ A) →ₗ[F] B)).ne'
  calc
    (∑ M : (V d ⧸ A) →ₗ[F] B,
      (∑ i : ι, c i * traceCharacter (φ i) M) * traceCharacter Z M) /
        (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ) =
      ∑ i : ι, c i *
        carrierMean A B (fun M => traceCharacter (φ i) M * traceCharacter Z M) := by
          simp only [carrierMean, div_eq_mul_inv]
          calc
            (∑ M : (V d ⧸ A) →ₗ[F] B,
                (∑ i : ι, c i * traceCharacter (φ i) M) * traceCharacter Z M) *
                  (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹ =
              (∑ i : ι, ∑ M : (V d ⧸ A) →ₗ[F] B,
                c i * traceCharacter (φ i) M * traceCharacter Z M) *
                  (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹ := by
                    congr 1
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro M _
                    rw [Finset.sum_mul]
            _ = ∑ i : ι, c i *
                  ((∑ M : (V d ⧸ A) →ₗ[F] B,
                    traceCharacter (φ i) M * traceCharacter Z M) *
                    (Fintype.card ((V d ⧸ A) →ₗ[F] B) : ℝ)⁻¹) := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro i _
                    have hs : (∑ M : (V d ⧸ A) →ₗ[F] B,
                        c i * traceCharacter (φ i) M * traceCharacter Z M) =
                        c i * ∑ M : (V d ⧸ A) →ₗ[F] B,
                          traceCharacter (φ i) M * traceCharacter Z M := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro M _
                      ring
                    rw [hs]
                    ring
    _ = ∑ i : ι, if φ i = Z then c i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [carrierCharacter_orthogonality]
          split_ifs <;> simp_all

theorem initialDerivative_character_sum {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → ℝ)
    (N : (V d ⧸ A) →ₗ[F] B) :
    initialDerivative A B T f N =
      ∑ Y : BinaryMatrix n d,
        (if Selected A B Y.transpose.toLin' then
          fourierCoeff f Y * traceCharacter Y.transpose.toLin' T else 0) *
          traceCharacter (induced A B Y.transpose.toLin') N := by
  unfold initialDerivative
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hY : Selected A B Y.transpose.toLin'
  · simp only [if_pos hY]
    rw [traceCharacter_carrier_base]
    simp only [induced]
    ring
  · simp [hY]

theorem initialDerivative_fourierCoeff {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (f : BinaryMatrix n d → ℝ)
    (Z : B →ₗ[F] (V d ⧸ A)) :
    carrierFourierCoeff A B (initialDerivative A B T f) Z =
      ∑ Y : BinaryMatrix n d,
        if induced A B Y.transpose.toLin' = Z then
          (if Selected A B Y.transpose.toLin' then
            fourierCoeff f Y * traceCharacter Y.transpose.toLin' T else 0)
        else 0 := by
  have hfun : initialDerivative A B T f =
      fun N => ∑ Y : BinaryMatrix n d,
        (if Selected A B Y.transpose.toLin' then
          fourierCoeff f Y * traceCharacter Y.transpose.toLin' T else 0) *
          traceCharacter (induced A B Y.transpose.toLin') N := by
    funext N
    exact initialDerivative_character_sum A B T f N
  rw [hfun]
  exact carrierFourierCoeff_sum_characters A B _ _ Z

end
end PvNP.RealizableHardness.BinaryMatrixA1CoefficientTransfer
