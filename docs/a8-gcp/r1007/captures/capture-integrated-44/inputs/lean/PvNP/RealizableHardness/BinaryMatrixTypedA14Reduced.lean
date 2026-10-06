import PvNP.RealizableHardness.BinaryMatrixTypedA14Line

namespace PvNP.RealizableHardness.BinaryMatrixTypedA14Reduced

open BinaryMatrixTypedA14Line BinaryMatrixTypedA15Reduced
open BinaryMatrixTypedA15OneStep BinaryMatrixTypedA15Transport
open BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixA1Phase BinaryMatrixA1Complex BinaryMatrixFourier
open BinaryMatrixComplexA14 BinaryMatrixFirstDerivative BinaryMatrixLineA15
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

private noncomputable instance reducedCarrierFintype {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) :
    Fintype (((V d ⧸ A) ⧸ L) →ₗ[F] B) := by
  classical
  letI : Fintype ((V d ⧸ A) ⧸ L) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

private noncomputable instance reducedFrequencyFintype {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) :
    Fintype (B →ₗ[F] ((V d ⧸ A) ⧸ L)) := by
  classical
  letI : Fintype ((V d ⧸ A) ⧸ L) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

def reducedFrequencyEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A)) :
    (B →ₗ[F] ((V d ⧸ A) ⧸ L)) ≃ₗ[F]
      BinaryMatrix (Module.finrank F B)
        (Module.finrank F ((V d ⧸ A) ⧸ L)) :=
  ((LinearEquiv.arrowCongr (codomainBasis B).equivFun
      (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun).trans
    LinearMap.toMatrix').trans (Matrix.transposeLinearEquiv _ _ F F)

theorem reducedFrequency_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (Y : B →ₗ[F] ((V d ⧸ A) ⧸ L)) :
    (reducedFrequencyEquiv B L Y).transpose.toLin' =
      (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.toLinearMap.comp
        (Y.comp (codomainBasis B).equivFun.symm.toLinearMap) := by
  simp only [reducedFrequencyEquiv, LinearEquiv.trans_apply,
    Matrix.transposeLinearEquiv_apply]
  apply LinearMap.ext
  intro x
  simp [LinearEquiv.arrowCongr_apply]

theorem reducedMatrix_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    (reducedMatrixEquiv B L M).toLin' =
      (codomainBasis B).equivFun.toLinearMap.comp
        (M.comp (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  change (reducedMatrixEquiv B L M).mulVec x =
    (codomainBasis B).equivFun
      (M ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm x))
  have h := reducedMatrix_mulVec B L M
    ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm x)
  rw [(Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.apply_symm_apply] at h
  exact h

theorem reducedFrequency_tracePair {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (Y : B →ₗ[F] ((V d ⧸ A) ⧸ L))
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    tracePair Y M =
      pairing (reducedFrequencyEquiv B L Y) (reducedMatrixEquiv B L M) := by
  rw [← BinaryMatrixA1CharacterBridge.tracePair_matrix,
    reducedFrequency_toLin, reducedMatrix_toLin]
  unfold tracePair
  let eU := (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun
  have hc :
      (eU.toLinearMap.comp
          (Y.comp (codomainBasis B).equivFun.symm.toLinearMap)).comp
        ((codomainBasis B).equivFun.toLinearMap.comp
          (M.comp eU.symm.toLinearMap)) = eU.conj (Y.comp M) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hc, LinearMap.trace_conj']

theorem reducedFrequency_rank {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (Y : B →ₗ[F] ((V d ⧸ A) ⧸ L)) :
    (reducedFrequencyEquiv B L Y).rank =
      Module.finrank F (LinearMap.range Y) := by
  rw [← Matrix.rank_transpose (reducedFrequencyEquiv B L Y)]
  rw [Matrix.rank_eq_finrank_range_toLin
    (reducedFrequencyEquiv B L Y).transpose
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin', reducedFrequency_toLin]
  have hpre : LinearMap.range
      (Y.comp (codomainBasis B).equivFun.symm.toLinearMap) =
      LinearMap.range Y := by
    rw [LinearMap.range_comp]
    simp
  rw [LinearMap.range_comp, hpre]
  exact (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.finrank_map_eq
    (LinearMap.range Y)

theorem reducedFrequency_character {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (Y : B →ₗ[F] ((V d ⧸ A) ⧸ L))
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    traceCharacter Y M =
      character (reducedFrequencyEquiv B L Y) (reducedMatrixEquiv B L M) := by
  rw [traceCharacter, character, reducedFrequency_tracePair]

def reducedComplexFourierCoeff {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] ((V d ⧸ A) ⧸ L)) : ℂ :=
  (∑ M : ((V d ⧸ A) ⧸ L) →ₗ[F] B,
    f M * (traceCharacter Y M : ℂ)) /
    (Fintype.card (((V d ⧸ A) ⧸ L) →ₗ[F] B) : ℂ)

theorem reducedFourierCoeff_coordinate {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] ((V d ⧸ A) ⧸ L)) :
    reducedComplexFourierCoeff B L f Y =
      complexFourierCoeff (fun X => f ((reducedMatrixEquiv B L).symm X))
        (reducedFrequencyEquiv B L Y) := by
  unfold reducedComplexFourierCoeff complexFourierCoeff
  have hs :
      (∑ M : ((V d ⧸ A) ⧸ L) →ₗ[F] B,
        f M * (traceCharacter Y M : ℂ)) =
      ∑ X : BinaryMatrix (Module.finrank F B)
          (Module.finrank F ((V d ⧸ A) ⧸ L)),
        f ((reducedMatrixEquiv B L).symm X) *
          (character (reducedFrequencyEquiv B L Y) X : ℂ) := by
    apply Fintype.sum_equiv (reducedMatrixEquiv B L).toEquiv
    intro M
    rw [reducedFrequency_character B L Y M]
    simp
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr (reducedMatrixEquiv B L).toEquiv

def reducedComplexRankProjection {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F)) (L : Submodule F (V d ⧸ A))
    (j : ℕ) (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ)
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (B →ₗ[F] ((V d ⧸ A) ⧸ L))).filter
      (fun Y => Module.finrank F (LinearMap.range Y) = j),
    reducedComplexFourierCoeff B L f Y * (traceCharacter Y M : ℂ)

theorem reducedRankProjection_coordinate {n d j : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ)
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    reducedComplexRankProjection B L j f M =
      complexRankProjection j
        (fun X => f ((reducedMatrixEquiv B L).symm X))
        (reducedMatrixEquiv B L M) := by
  unfold reducedComplexRankProjection complexRankProjection
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (reducedFrequencyEquiv B L).toEquiv
  intro Y
  rw [← reducedFrequency_rank B L Y,
    reducedFourierCoeff_coordinate B L f Y,
    reducedFrequency_character B L Y M]
  simp

end
end PvNP.RealizableHardness.BinaryMatrixTypedA14Reduced
