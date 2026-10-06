import PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal
import PvNP.RealizableHardness.BinaryMatrixA1Complex

namespace PvNP.RealizableHardness.BinaryMatrixTypedA14Line

open BinaryMatrixTypedA15OneStep BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixTypedA15Transport BinaryMatrixA1Phase
open BinaryMatrixFourier BinaryMatrixA1CharacterBridge
open BinaryMatrixA1Complex
open BinaryMatrixComplexA14
open BinaryMatrixHybridSelector
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

def lineFrequencyEquiv {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1) :
    (B →ₗ[F] (V d ⧸ A)) ≃ₗ[F]
      BinaryMatrix (Module.finrank F B)
        (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) :=
  ((LinearEquiv.arrowCongr (codomainBasis B).equivFun
      (lineAdaptedEquiv L hL)).trans LinearMap.toMatrix').trans
    (Matrix.transposeLinearEquiv _ _ F F)

theorem lineFrequency_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    (lineFrequencyEquiv B L hL Y).transpose.toLin' =
      (lineAdaptedEquiv L hL).toLinearMap.comp
        (Y.comp (codomainBasis B).equivFun.symm.toLinearMap) := by
  simp only [lineFrequencyEquiv, LinearEquiv.trans_apply,
    Matrix.transposeLinearEquiv_apply]
  apply LinearMap.ext
  intro x
  simp [LinearEquiv.arrowCongr_apply]

theorem lineMatrix_toLin {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (M : (V d ⧸ A) →ₗ[F] B) :
    (lineMatrixEquiv B L hL M).toLin' =
      (codomainBasis B).equivFun.toLinearMap.comp
        (M.comp (lineAdaptedEquiv L hL).symm.toLinearMap) := by
  simp only [lineMatrixEquiv, LinearEquiv.trans_apply]
  apply LinearMap.ext
  intro x
  simp [LinearEquiv.arrowCongr_apply]

theorem lineFrequency_tracePair {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) (M : (V d ⧸ A) →ₗ[F] B) :
    tracePair Y M =
      pairing (lineFrequencyEquiv B L hL Y) (lineMatrixEquiv B L hL M) := by
  rw [← tracePair_matrix, lineFrequency_toLin, lineMatrix_toLin]
  unfold tracePair
  have hc :
      ((lineAdaptedEquiv L hL).toLinearMap.comp
          (Y.comp (codomainBasis B).equivFun.symm.toLinearMap)).comp
        ((codomainBasis B).equivFun.toLinearMap.comp
          (M.comp (lineAdaptedEquiv L hL).symm.toLinearMap)) =
      (lineAdaptedEquiv L hL).conj (Y.comp M) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hc, LinearMap.trace_conj']

theorem lineFrequency_rank {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    (lineFrequencyEquiv B L hL Y).rank =
      Module.finrank F (LinearMap.range Y) := by
  rw [← Matrix.rank_transpose (lineFrequencyEquiv B L hL Y)]
  rw [Matrix.rank_eq_finrank_range_toLin
    (lineFrequencyEquiv B L hL Y).transpose
    (Pi.basisFun F _) (Pi.basisFun F _)]
  rw [Matrix.toLin_eq_toLin', lineFrequency_toLin]
  have hpre : LinearMap.range
      (Y.comp (codomainBasis B).equivFun.symm.toLinearMap) =
      LinearMap.range Y := by
    rw [LinearMap.range_comp]
    simp
  rw [LinearMap.range_comp, hpre]
  exact (lineAdaptedEquiv L hL).finrank_map_eq (LinearMap.range Y)

theorem lineFrequency_character {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) (M : (V d ⧸ A) →ₗ[F] B) :
    traceCharacter Y M =
      character (lineFrequencyEquiv B L hL Y) (lineMatrixEquiv B L hL M) := by
  rw [traceCharacter, character, lineFrequency_tracePair]

theorem lineFourierCoeff_coordinate {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    complexCarrierFourierCoeff A B f Y =
      complexFourierCoeff (fun X => f ((lineMatrixEquiv B L hL).symm X))
        (lineFrequencyEquiv B L hL Y) := by
  unfold complexCarrierFourierCoeff complexFourierCoeff
  have hs :
      (∑ M : (V d ⧸ A) →ₗ[F] B, f M * (traceCharacter Y M : ℂ)) =
      ∑ X : BinaryMatrix (Module.finrank F B)
          (Module.finrank F ((V d ⧸ A) ⧸ L) + 1),
        f ((lineMatrixEquiv B L hL).symm X) *
          (character (lineFrequencyEquiv B L hL Y) X : ℂ) := by
    apply Fintype.sum_equiv (lineMatrixEquiv B L hL).toEquiv
    intro M
    rw [lineFrequency_character B L hL Y M]
    simp
  rw [hs]
  congr 1
  exact_mod_cast Fintype.card_congr (lineMatrixEquiv B L hL).toEquiv

def typedComplexRankProjection {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (j : ℕ) (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (B →ₗ[F] (V d ⧸ A))).filter
      (fun Y => Module.finrank F (LinearMap.range Y) = j),
    complexCarrierFourierCoeff A B f Y * (traceCharacter Y M : ℂ)

theorem typedRankProjection_lineCoordinate {n d j : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedComplexRankProjection A B j f M =
      complexRankProjection j
        (fun X => f ((lineMatrixEquiv B L hL).symm X))
        (lineMatrixEquiv B L hL M) := by
  unfold typedComplexRankProjection complexRankProjection
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (lineFrequencyEquiv B L hL).toEquiv
  intro Y
  rw [← lineFrequency_rank B L hL Y,
    lineFourierCoeff_coordinate B L hL f Y,
    lineFrequency_character B L hL Y M]
  simp

def typedLineSelected {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) : Prop :=
  (↑((lineScalarEquiv L hL).symm 1) : V d ⧸ A) ∈ LinearMap.range Y

theorem typedLineSelected_coordinate {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    typedLineSelected B L hL Y ↔
      hybridLineSelected (lineFrequencyEquiv B L hL Y) := by
  let eU := lineAdaptedEquiv L hL
  let eZ := (codomainBasis B).equivFun
  have hrange : LinearMap.range
      (lineFrequencyEquiv B L hL Y).transpose.toLin' =
      (LinearMap.range Y).map eU.toLinearMap := by
    rw [lineFrequency_toLin, LinearMap.range_comp]
    have he : LinearMap.range (Y.comp eZ.symm.toLinearMap) =
        LinearMap.range Y := by
      rw [LinearMap.range_comp]
      simp
    rw [he]
  have hlast : eU ((lineScalarEquiv L hL).symm 1 : L) =
      Pi.single (Fin.last (Module.finrank F ((V d ⧸ A) ⧸ L))) 1 := by
    rw [← lineAdapted_symm_last L hL]
    simp [eU]
  unfold typedLineSelected hybridLineSelected
  rw [← Matrix.toLin'_apply', hrange, ← hlast]
  simp

def typedComplexLineFilter {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) : ℂ :=
  ∑ Y ∈ (Finset.univ : Finset (B →ₗ[F] (V d ⧸ A))).filter
      (typedLineSelected B L hL),
    complexCarrierFourierCoeff A B f Y * (traceCharacter Y M : ℂ)

theorem typedLineFilter_coordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (M : (V d ⧸ A) →ₗ[F] B) :
    typedComplexLineFilter B L hL f M =
      complexHybridLineFilter
        (fun X => f ((lineMatrixEquiv B L hL).symm X))
        (lineMatrixEquiv B L hL M) := by
  unfold typedComplexLineFilter complexHybridLineFilter
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (lineFrequencyEquiv B L hL).toEquiv
  intro Y
  rw [typedLineSelected_coordinate B L hL Y,
    lineFourierCoeff_coordinate B L hL f Y,
    lineFrequency_character B L hL Y M]
  simp

end
end PvNP.RealizableHardness.BinaryMatrixTypedA14Line
