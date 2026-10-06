import PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReducedGlobal
import PvNP.RealizableHardness.BinaryMatrixTypedA14Line

namespace PvNP.RealizableHardness.BinaryMatrixTypedA14Hyperplane

open BinaryMatrixTypedA15Hyperplane BinaryMatrixTypedA15HyperplaneGlobal
open BinaryMatrixTypedA15Transport BinaryMatrixTypedA14Line
open BinaryMatrixA1Phase BinaryMatrixFourier BinaryMatrixA1CharacterBridge
open BinaryMatrixA1Complex BinaryMatrixComplexA14 BinaryMatrixHybridSelector
open BinaryMatrixComplexA15 BinaryMatrixCodomainA14
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

private noncomputable instance carrierFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F)) :
    Fintype ((V d ⧸ A) →ₗ[F] B) := by
  classical
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

private noncomputable instance frequencyFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F)) :
    Fintype (B →ₗ[F] (V d ⧸ A)) := by
  classical
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

def hyperplaneFrequencyEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    (B →ₗ[F] (V d ⧸ A)) ≃ₗ[F]
      BinaryMatrix (Module.finrank F H + 1)
        (Module.finrank F (V d ⧸ A)) :=
  ((LinearEquiv.arrowCongr (hyperplaneAdaptedEquiv B H hH)
      ((domainBasis A).equivFun)).trans LinearMap.toMatrix').trans
    (Matrix.transposeLinearEquiv _ _ F F)

theorem hyperplaneFrequency_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    (hyperplaneFrequencyEquiv B H hH Y).transpose.toLin' =
      ((domainBasis A).equivFun).toLinearMap.comp
        (Y.comp (hyperplaneAdaptedEquiv B H hH).symm.toLinearMap) := by
  simp only [hyperplaneFrequencyEquiv, LinearEquiv.trans_apply,
    Matrix.transposeLinearEquiv_apply]
  apply LinearMap.ext
  intro x
  simp [LinearEquiv.arrowCongr_apply]

theorem hyperplaneMatrix_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M : (V d ⧸ A) →ₗ[F] B) :
    (hyperplaneMatrixEquiv B H hH M).toLin' =
      (hyperplaneAdaptedEquiv B H hH).toLinearMap.comp
        (M.comp ((domainBasis A).equivFun).symm.toLinearMap) := by
  simp only [hyperplaneMatrixEquiv, LinearEquiv.trans_apply]
  apply LinearMap.ext
  intro x
  simp [LinearEquiv.arrowCongr_apply]

theorem hyperplaneFrequency_tracePair {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) (M : (V d ⧸ A) →ₗ[F] B) :
    tracePair Y M =
      pairing (hyperplaneFrequencyEquiv B H hH Y) (hyperplaneMatrixEquiv B H hH M) := by
  rw [← tracePair_matrix, hyperplaneFrequency_toLin, hyperplaneMatrix_toLin]
  unfold tracePair
  have hc :
      (((domainBasis A).equivFun).toLinearMap.comp
          (Y.comp (hyperplaneAdaptedEquiv B H hH).symm.toLinearMap)).comp
        ((hyperplaneAdaptedEquiv B H hH).toLinearMap.comp
          (M.comp ((domainBasis A).equivFun).symm.toLinearMap)) =
      ((domainBasis A).equivFun).conj (Y.comp M) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hc, LinearMap.trace_conj']

theorem hyperplaneFrequency_rank {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    (hyperplaneFrequencyEquiv B H hH Y).rank =
      Module.finrank F (LinearMap.range Y) := by
  rw [← Matrix.rank_transpose (hyperplaneFrequencyEquiv B H hH Y)]
  rw [Matrix.rank_eq_finrank_range_toLin
    (hyperplaneFrequencyEquiv B H hH Y).transpose
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin', hyperplaneFrequency_toLin]
  have hpre : LinearMap.range
      (Y.comp (hyperplaneAdaptedEquiv B H hH).symm.toLinearMap) =
      LinearMap.range Y := by
    rw [LinearMap.range_comp]
    simp
  rw [LinearMap.range_comp, hpre]
  exact ((domainBasis A).equivFun).finrank_map_eq (LinearMap.range Y)

theorem hyperplaneFrequency_character {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) (M : (V d ⧸ A) →ₗ[F] B) :
    traceCharacter Y M =
      character (hyperplaneFrequencyEquiv B H hH Y) (hyperplaneMatrixEquiv B H hH M) := by
  rw [traceCharacter, character, hyperplaneFrequency_tracePair]

theorem hyperplaneFourierCoeff_coordinate {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    complexCarrierFourierCoeff A B f Y =
      complexFourierCoeff (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X))
        (hyperplaneFrequencyEquiv B H hH Y) := by
  unfold complexCarrierFourierCoeff complexFourierCoeff
  have hs :
      (∑ M : (V d ⧸ A) →ₗ[F] B, f M * (traceCharacter Y M : ℂ)) =
      ∑ X : BinaryMatrix (Module.finrank F H + 1)
          (Module.finrank F (V d ⧸ A)),
        f ((hyperplaneMatrixEquiv B H hH).symm X) *
          (character (hyperplaneFrequencyEquiv B H hH Y) X : ℂ) := by
    apply Fintype.sum_equiv (hyperplaneMatrixEquiv B H hH).toEquiv
    intro M
    rw [hyperplaneFrequency_character B H hH Y M]
    simp
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr (hyperplaneMatrixEquiv B H hH).toEquiv

theorem typedRankProjection_hyperplaneCoordinate {n d j : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedComplexRankProjection A B j f M =
      complexRankProjection j
        (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X))
        (hyperplaneMatrixEquiv B H hH M) := by
  unfold typedComplexRankProjection complexRankProjection
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (hyperplaneFrequencyEquiv B H hH).toEquiv
  intro Y
  rw [← hyperplaneFrequency_rank B H hH Y,
    hyperplaneFourierCoeff_coordinate B H hH f Y,
    hyperplaneFrequency_character B H hH Y M]
  simp

theorem complexFourierCoeff_transpose {p q : ℕ}
    (g : BinaryMatrix p q → ℂ) (Y : BinaryMatrix p q) :
    complexFourierCoeff (complexTranspose g) Y.transpose =
      complexFourierCoeff g Y := by
  apply Complex.ext
  · simp only [complexFourierCoeff_re]
    exact fourierCoeff_transpose (fun X => (g X).re) Y
  · simp only [complexFourierCoeff_im]
    exact fourierCoeff_transpose (fun X => (g X).im) Y

def typedHyperplaneSelected {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) : Prop :=
  hybridLineSelected (hyperplaneFrequencyEquiv B H hH Y).transpose

def typedComplexHyperplaneFilter {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (B →ₗ[F] (V d ⧸ A))).filter
      (typedHyperplaneSelected B H hH),
    complexCarrierFourierCoeff A B f Y * (traceCharacter Y M : ℂ)

theorem typedHyperplaneFilter_coordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedComplexHyperplaneFilter B H hH f M =
      complexHybridLineFilter
        (complexTranspose (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X)))
        (hyperplaneMatrixEquiv B H hH M).transpose := by
  unfold typedComplexHyperplaneFilter complexHybridLineFilter
  simp only [Finset.sum_filter]
  let e : (B →ₗ[F] (V d ⧸ A)) ≃ₗ[F]
      BinaryMatrix (Module.finrank F (V d ⧸ A)) (Module.finrank F H + 1) :=
    (hyperplaneFrequencyEquiv B H hH).trans
    (Matrix.transposeLinearEquiv _ _ F F)
  apply Fintype.sum_equiv e.toEquiv
  intro Y
  rw [hyperplaneFourierCoeff_coordinate B H hH f Y,
    hyperplaneFrequency_character B H hH Y M]
  simp [e, typedHyperplaneSelected, complexFourierCoeff_transpose,
    character_transpose]
  rfl


end
end PvNP.RealizableHardness.BinaryMatrixTypedA14Hyperplane
