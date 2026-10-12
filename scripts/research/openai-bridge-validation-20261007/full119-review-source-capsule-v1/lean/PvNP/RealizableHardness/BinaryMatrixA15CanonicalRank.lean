import PvNP.RealizableHardness.BinaryMatrixA15NestedHyperplane
import PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneReduced

namespace PvNP.RealizableHardness.BinaryMatrixA15CanonicalRank

open BinaryMatrixA15NestedHyperplane
open BinaryMatrixTypedA14HyperplaneReduced
open BinaryMatrixTypedA14Line
open BinaryMatrixA1Phase
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def hyperplaneCanonicalFrequencyEquiv {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) :
    (H →ₗ[F] (V d ⧸ A)) ≃ₗ[F]
      (hyperplaneCanonicalCodomain B H →ₗ[F] (V d ⧸ A)) :=
  LinearEquiv.arrowCongr (hyperplaneCanonicalCodomainEquiv B H)
    (LinearEquiv.refl F (V d ⧸ A))

theorem hyperplaneCanonicalFrequency_apply {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (Y : H →ₗ[F] (V d ⧸ A))
    (z : hyperplaneCanonicalCodomain B H) :
    hyperplaneCanonicalFrequencyEquiv B H Y z =
      Y ((hyperplaneCanonicalCodomainEquiv B H).symm z) := by
  simp [hyperplaneCanonicalFrequencyEquiv]

theorem hyperplaneCanonical_tracePair {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (Y : H →ₗ[F] (V d ⧸ A))
    (M : (V d ⧸ A) →ₗ[F] H) :
    tracePair (hyperplaneCanonicalFrequencyEquiv B H Y)
        (hyperplaneCanonicalEquiv B H M) = tracePair Y M := by
  have hc :
      (hyperplaneCanonicalFrequencyEquiv B H Y).comp
          (hyperplaneCanonicalEquiv B H M) = Y.comp M := by
    ext u
    simp [hyperplaneCanonicalFrequency_apply,
      hyperplaneCanonicalEquiv_apply]
  simpa [tracePair] using congrArg (LinearMap.trace F (V d ⧸ A)) hc

theorem hyperplaneCanonical_character {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (Y : H →ₗ[F] (V d ⧸ A))
    (M : (V d ⧸ A) →ₗ[F] H) :
    traceCharacter (hyperplaneCanonicalFrequencyEquiv B H Y)
        (hyperplaneCanonicalEquiv B H M) = traceCharacter Y M := by
  simp [traceCharacter, hyperplaneCanonical_tracePair]

theorem hyperplaneCanonical_frequency_rank {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (Y : H →ₗ[F] (V d ⧸ A)) :
    Module.finrank F (LinearMap.range (hyperplaneCanonicalFrequencyEquiv B H Y)) =
      Module.finrank F (LinearMap.range Y) := by
  have hr : LinearMap.range (hyperplaneCanonicalFrequencyEquiv B H Y) =
      LinearMap.range Y := by
    change LinearMap.range (Y.comp
      (hyperplaneCanonicalCodomainEquiv B H).symm.toLinearMap) = _
    rw [LinearMap.range_comp]
    simp
  rw [hr]

theorem hyperplaneCanonical_fourierCoeff {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ)
    (Y : H →ₗ[F] (V d ⧸ A)) :
    BinaryMatrixA1Complex.complexCarrierFourierCoeff A
        (hyperplaneCanonicalCodomain B H)
        (fun M => f ((hyperplaneCanonicalEquiv B H).symm M))
        (hyperplaneCanonicalFrequencyEquiv B H Y) =
      hyperplaneReducedComplexFourierCoeff B H hH f Y := by
  unfold BinaryMatrixA1Complex.complexCarrierFourierCoeff
    hyperplaneReducedComplexFourierCoeff
  have hs :
      (∑ M : (V d ⧸ A) →ₗ[F] hyperplaneCanonicalCodomain B H,
        f ((hyperplaneCanonicalEquiv B H).symm M) *
          (traceCharacter (hyperplaneCanonicalFrequencyEquiv B H Y) M : ℂ)) =
        ∑ M : (V d ⧸ A) →ₗ[F] H,
          f M * (traceCharacter Y M : ℂ) := by
    apply Fintype.sum_equiv (hyperplaneCanonicalEquiv B H).symm.toEquiv
    intro M
    have hc := hyperplaneCanonical_character B H Y
      ((hyperplaneCanonicalEquiv B H).symm M)
    simp only [LinearEquiv.apply_symm_apply] at hc
    rw [hc]
    simp
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr (hyperplaneCanonicalEquiv B H).symm.toEquiv

theorem hyperplaneCanonical_rankProjection {n d j : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] H) :
    BinaryMatrixTypedA14Line.typedComplexRankProjection A
        (hyperplaneCanonicalCodomain B H) j
        (fun X => f ((hyperplaneCanonicalEquiv B H).symm X))
        (hyperplaneCanonicalEquiv B H M) =
      hyperplaneReducedComplexRankProjection B H hH j f M := by
  unfold BinaryMatrixTypedA14Line.typedComplexRankProjection
    hyperplaneReducedComplexRankProjection
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (hyperplaneCanonicalFrequencyEquiv B H).symm.toEquiv
  intro Y
  have hf := hyperplaneCanonical_fourierCoeff B H hH f
    ((hyperplaneCanonicalFrequencyEquiv B H).symm Y)
  have hr := hyperplaneCanonical_frequency_rank B H
    ((hyperplaneCanonicalFrequencyEquiv B H).symm Y)
  have hc := hyperplaneCanonical_character B H
    ((hyperplaneCanonicalFrequencyEquiv B H).symm Y) M
  simp only [LinearEquiv.apply_symm_apply] at hf hr hc
  change (if Module.finrank F (LinearMap.range Y) = j then
      BinaryMatrixA1Complex.complexCarrierFourierCoeff A
        (hyperplaneCanonicalCodomain B H)
        (fun X => f ((hyperplaneCanonicalEquiv B H).symm X)) Y *
        (traceCharacter Y (hyperplaneCanonicalEquiv B H M) : ℂ) else 0) =
    (if Module.finrank F (LinearMap.range
        ((hyperplaneCanonicalFrequencyEquiv B H).symm Y)) = j then
      hyperplaneReducedComplexFourierCoeff B H hH f
        ((hyperplaneCanonicalFrequencyEquiv B H).symm Y) *
        (traceCharacter ((hyperplaneCanonicalFrequencyEquiv B H).symm Y) M : ℂ)
      else 0)
  rw [← hf, ← hc]
  have he : hyperplaneCanonicalFrequencyEquiv B H
      ((hyperplaneCanonicalFrequencyEquiv B H).symm Y) = Y :=
    (hyperplaneCanonicalFrequencyEquiv B H).apply_symm_apply Y
  rw [he] at hr
  rw [hr]

end
end PvNP.RealizableHardness.BinaryMatrixA15CanonicalRank
