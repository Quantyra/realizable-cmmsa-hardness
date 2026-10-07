import PvNP.RealizableHardness.BinaryMatrixTypedA14Hyperplane

namespace PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneReduced

open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15HyperplaneReduced
open BinaryMatrixTypedA15HyperplaneReducedGlobal
open BinaryMatrixA1Phase BinaryMatrixA1CharacterBridge BinaryMatrixA1Complex
open BinaryMatrixFourier BinaryMatrixComplexA14 BinaryMatrixTypedA14Hyperplane
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

private noncomputable instance reducedCarrierFintype {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) :
    Fintype ((V d ⧸ A) →ₗ[F] H) := by
  classical
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype H := Fintype.ofFinite _
  exact FunLike.fintype _

private noncomputable instance reducedFrequencyFintype {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) :
    Fintype (H →ₗ[F] (V d ⧸ A)) := by
  classical
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype H := Fintype.ofFinite _
  exact FunLike.fintype _

def hyperplaneReducedFrequencyEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1) :
    (H →ₗ[F] (V d ⧸ A)) ≃ₗ[F]
      BinaryMatrix (Module.finrank F H)
        (Module.finrank F (V d ⧸ A)) :=
  ((LinearEquiv.arrowCongr (Module.finBasis F H).equivFun
      (domainBasis A).equivFun).trans
    LinearMap.toMatrix').trans (Matrix.transposeLinearEquiv _ _ F F)

theorem hyperplaneReducedFrequency_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : H →ₗ[F] (V d ⧸ A)) :
    (hyperplaneReducedFrequencyEquiv B H hH Y).transpose.toLin' =
      (domainBasis A).equivFun.toLinearMap.comp
        (Y.comp (Module.finBasis F H).equivFun.symm.toLinearMap) := by
  simp only [hyperplaneReducedFrequencyEquiv, LinearEquiv.trans_apply,
    Matrix.transposeLinearEquiv_apply]
  apply LinearMap.ext
  intro x
  simp [LinearEquiv.arrowCongr_apply]

theorem hyperplaneReducedMatrix_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M : (V d ⧸ A) →ₗ[F] H) :
    (hyperplaneReducedMatrixEquiv H M).toLin' =
      (Module.finBasis F H).equivFun.toLinearMap.comp
        (M.comp (domainBasis A).equivFun.symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  change (hyperplaneReducedMatrixEquiv H M).mulVec x =
    (Module.finBasis F H).equivFun
      (M ((domainBasis A).equivFun.symm x))
  have h := reducedMatrix_mulVec B H hH M
    ((domainBasis A).equivFun.symm x)
  rw [(domainBasis A).equivFun.apply_symm_apply] at h
  exact h

theorem hyperplaneReducedFrequency_tracePair {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : H →ₗ[F] (V d ⧸ A))
    (M : (V d ⧸ A) →ₗ[F] H) :
    tracePair Y M =
      pairing (hyperplaneReducedFrequencyEquiv B H hH Y) (hyperplaneReducedMatrixEquiv H M) := by
  rw [← BinaryMatrixA1CharacterBridge.tracePair_matrix,
    hyperplaneReducedFrequency_toLin B H hH,
    hyperplaneReducedMatrix_toLin B H hH]
  unfold tracePair
  let eU := (domainBasis A).equivFun
  have hc :
      (eU.toLinearMap.comp
          (Y.comp (Module.finBasis F H).equivFun.symm.toLinearMap)).comp
        ((Module.finBasis F H).equivFun.toLinearMap.comp
          (M.comp eU.symm.toLinearMap)) = eU.conj (Y.comp M) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hc, LinearMap.trace_conj']

theorem hyperplaneReducedFrequency_rank {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : H →ₗ[F] (V d ⧸ A)) :
    (hyperplaneReducedFrequencyEquiv B H hH Y).rank =
      Module.finrank F (LinearMap.range Y) := by
  rw [← Matrix.rank_transpose (hyperplaneReducedFrequencyEquiv B H hH Y)]
  rw [Matrix.rank_eq_finrank_range_toLin
    (hyperplaneReducedFrequencyEquiv B H hH Y).transpose
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin', hyperplaneReducedFrequency_toLin]
  have hpre : LinearMap.range
      (Y.comp (Module.finBasis F H).equivFun.symm.toLinearMap) =
      LinearMap.range Y := by
    rw [LinearMap.range_comp]
    simp
  rw [LinearMap.range_comp, hpre]
  exact (domainBasis A).equivFun.finrank_map_eq
    (LinearMap.range Y)

theorem hyperplaneReducedFrequency_character {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Y : H →ₗ[F] (V d ⧸ A))
    (M : (V d ⧸ A) →ₗ[F] H) :
    traceCharacter Y M =
      character (hyperplaneReducedFrequencyEquiv B H hH Y) (hyperplaneReducedMatrixEquiv H M) := by
  rw [traceCharacter, character, hyperplaneReducedFrequency_tracePair]

def hyperplaneReducedComplexFourierCoeff {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ)
    (Y : H →ₗ[F] (V d ⧸ A)) : ℂ :=
  (∑ M : (V d ⧸ A) →ₗ[F] H,
    f M * (traceCharacter Y M : ℂ)) /
    (Fintype.card ((V d ⧸ A) →ₗ[F] H) : ℂ)

theorem hyperplaneReducedFourierCoeff_coordinate {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ)
    (Y : H →ₗ[F] (V d ⧸ A)) :
    hyperplaneReducedComplexFourierCoeff B H hH f Y =
      complexFourierCoeff (fun X => f ((hyperplaneReducedMatrixEquiv H).symm X))
        (hyperplaneReducedFrequencyEquiv B H hH Y) := by
  unfold hyperplaneReducedComplexFourierCoeff complexFourierCoeff
  have hs :
      (∑ M : (V d ⧸ A) →ₗ[F] H,
        f M * (traceCharacter Y M : ℂ)) =
      ∑ X : BinaryMatrix (Module.finrank F H)
          (Module.finrank F (V d ⧸ A)),
        f ((hyperplaneReducedMatrixEquiv H).symm X) *
          (character (hyperplaneReducedFrequencyEquiv B H hH Y) X : ℂ) := by
    apply Fintype.sum_equiv (hyperplaneReducedMatrixEquiv H).toEquiv
    intro M
    rw [hyperplaneReducedFrequency_character B H hH Y M]
    simp
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr (hyperplaneReducedMatrixEquiv H).toEquiv

def hyperplaneReducedComplexRankProjection {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (j : ℕ) (f : ((V d ⧸ A) →ₗ[F] H) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] H) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (H →ₗ[F] (V d ⧸ A))).filter
      (fun Y => Module.finrank F (LinearMap.range Y) = j),
    hyperplaneReducedComplexFourierCoeff B H hH f Y * (traceCharacter Y M : ℂ)

theorem hyperplaneReducedRankProjection_coordinate {n d j : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] H) :
    hyperplaneReducedComplexRankProjection B H hH j f M =
      complexRankProjection j
        (fun X => f ((hyperplaneReducedMatrixEquiv H).symm X))
        (hyperplaneReducedMatrixEquiv H M) := by
  unfold hyperplaneReducedComplexRankProjection complexRankProjection
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (hyperplaneReducedFrequencyEquiv B H hH).toEquiv
  intro Y
  rw [← hyperplaneReducedFrequency_rank B H hH Y,
    hyperplaneReducedFourierCoeff_coordinate B H hH f Y,
    hyperplaneReducedFrequency_character B H hH Y M]
  simp

end
end PvNP.RealizableHardness.BinaryMatrixTypedA14HyperplaneReduced
