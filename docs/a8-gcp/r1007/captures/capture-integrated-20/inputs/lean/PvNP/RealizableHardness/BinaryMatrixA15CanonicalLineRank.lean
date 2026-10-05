import PvNP.RealizableHardness.BinaryMatrixA15CanonicalRank
import PvNP.RealizableHardness.BinaryMatrixTypedA14Reduced

namespace PvNP.RealizableHardness.BinaryMatrixA15CanonicalLineRank

open BinaryMatrixA15NestedLine BinaryMatrixA1NestedCarrier
open BinaryMatrixTypedA14Reduced BinaryMatrixTypedA14Line
open BinaryMatrixA1Phase
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def lineCanonicalFrequencyEquiv {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁) :
    (B →ₗ[F] ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ)) ≃ₗ[F]
      (B →ₗ[F] (V d ⧸ A₁)) :=
  LinearEquiv.arrowCongr (LinearEquiv.refl F B)
    (nestedDomainEquiv A₂ A₁ hA)

theorem lineCanonicalFrequency_apply {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Y : B →ₗ[F] ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ)) (b : B) :
    lineCanonicalFrequencyEquiv A₂ A₁ B hA Y b =
      nestedDomainEquiv A₂ A₁ hA (Y b) := by
  simp [lineCanonicalFrequencyEquiv]

theorem lineCanonical_tracePair {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Y : B →ₗ[F] ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ))
    (M : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    tracePair (lineCanonicalFrequencyEquiv A₂ A₁ B hA Y)
        (lineCanonicalEquiv A₂ A₁ B hA M) = tracePair Y M := by
  let e := nestedDomainEquiv A₂ A₁ hA
  have hc : (lineCanonicalFrequencyEquiv A₂ A₁ B hA Y).comp
      (lineCanonicalEquiv A₂ A₁ B hA M) = e.conj (Y.comp M) := by
    ext u
    simp [lineCanonicalFrequency_apply, lineCanonicalEquiv_apply,
      LinearEquiv.conj_apply, e]
  unfold tracePair
  rw [hc, LinearMap.trace_conj']

theorem lineCanonical_character {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Y : B →ₗ[F] ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ))
    (M : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    traceCharacter (lineCanonicalFrequencyEquiv A₂ A₁ B hA Y)
        (lineCanonicalEquiv A₂ A₁ B hA M) = traceCharacter Y M := by
  simp [traceCharacter, lineCanonical_tracePair]

theorem lineCanonical_frequency_rank {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Y : B →ₗ[F] ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ)) :
    Module.finrank F (LinearMap.range (lineCanonicalFrequencyEquiv A₂ A₁ B hA Y)) =
      Module.finrank F (LinearMap.range Y) := by
  change Module.finrank F (LinearMap.range
    ((nestedDomainEquiv A₂ A₁ hA).toLinearMap.comp Y)) = _
  rw [LinearMap.range_comp]
  exact (nestedDomainEquiv A₂ A₁ hA).finrank_map_eq (LinearMap.range Y)

theorem lineCanonical_fourierCoeff {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (f : (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ)) :
    BinaryMatrixA1Complex.complexCarrierFourierCoeff A₁ B
        (fun M => f ((lineCanonicalEquiv A₂ A₁ B hA).symm M))
        (lineCanonicalFrequencyEquiv A₂ A₁ B hA Y) =
      reducedComplexFourierCoeff B (A₁.map A₂.mkQ) f Y := by
  unfold BinaryMatrixA1Complex.complexCarrierFourierCoeff
    reducedComplexFourierCoeff
  have hs :
      (∑ M : (V d ⧸ A₁) →ₗ[F] B,
        f ((lineCanonicalEquiv A₂ A₁ B hA).symm M) *
          (traceCharacter (lineCanonicalFrequencyEquiv A₂ A₁ B hA Y) M : ℂ)) =
        ∑ M : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B,
          f M * (traceCharacter Y M : ℂ) := by
    apply Fintype.sum_equiv (lineCanonicalEquiv A₂ A₁ B hA).symm.toEquiv
    intro M
    have hc := lineCanonical_character A₂ A₁ B hA Y
      ((lineCanonicalEquiv A₂ A₁ B hA).symm M)
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [hc]
    simp
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr (lineCanonicalEquiv A₂ A₁ B hA).symm.toEquiv

theorem lineCanonical_rankProjection {n d j : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (f : (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) → ℂ)
    (M : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    typedComplexRankProjection A₁ B j
        (fun X => f ((lineCanonicalEquiv A₂ A₁ B hA).symm X))
        (lineCanonicalEquiv A₂ A₁ B hA M) =
      reducedComplexRankProjection B (A₁.map A₂.mkQ) j f M := by
  unfold typedComplexRankProjection reducedComplexRankProjection
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm.toEquiv
  intro Y
  have hf := lineCanonical_fourierCoeff A₂ A₁ B hA f
    ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y)
  have hr := lineCanonical_frequency_rank A₂ A₁ B hA
    ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y)
  have hc := lineCanonical_character A₂ A₁ B hA
    ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y) M
  simp only [LinearEquiv.apply_symm_apply] at hf hr hc
  change (if Module.finrank F (LinearMap.range Y) = j then
      BinaryMatrixA1Complex.complexCarrierFourierCoeff A₁ B
        (fun X => f ((lineCanonicalEquiv A₂ A₁ B hA).symm X)) Y *
        (traceCharacter Y (lineCanonicalEquiv A₂ A₁ B hA M) : ℂ) else 0) =
    (if Module.finrank F (LinearMap.range
        ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y)) = j then
      reducedComplexFourierCoeff B (A₁.map A₂.mkQ) f
        ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y) *
        (traceCharacter ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y) M : ℂ)
      else 0)
  rw [← hf, ← hc]
  have he : lineCanonicalFrequencyEquiv A₂ A₁ B hA
      ((lineCanonicalFrequencyEquiv A₂ A₁ B hA).symm Y) = Y :=
    (lineCanonicalFrequencyEquiv A₂ A₁ B hA).apply_symm_apply Y
  rw [he] at hr
  rw [hr]

end
end PvNP.RealizableHardness.BinaryMatrixA15CanonicalLineRank
