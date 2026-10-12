import PvNP.RealizableHardness.BinaryMatrixTypedA15OneStep

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobal

open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15OneStep BinaryMatrixFourier
open BinaryMatrixFirstDerivative
open BinaryMatrixLineA15
open BinaryMatrixActualAffine BinaryMatrixComplexA15
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

def lineCoordinateRestriction {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B) :
    ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) where
  domainFixed := Q.domainFixed.map (lineAdaptedEquiv L hL).toLinearMap
  codomainVariation := Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap
  base := lineMatrixEquiv B L hL Q.base

theorem lineMatrix_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (M : (V d ⧸ A) →ₗ[F] B) (u : V d ⧸ A) :
    (lineMatrixEquiv B L hL M).mulVec (lineAdaptedEquiv L hL u) =
      (codomainBasis B).equivFun (M u) := by
  simp only [lineMatrixEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem lineMatrix_sub_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (M T : (V d ⧸ A) →ₗ[F] B) (u : V d ⧸ A) :
    (lineMatrixEquiv B L hL M - lineMatrixEquiv B L hL T).mulVec
        (lineAdaptedEquiv L hL u) =
      (codomainBasis B).equivFun ((M - T) u) := by
  rw [← map_sub]
  exact lineMatrix_mulVec B L hL (M - T) u

private theorem mem_line_domain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B)
    (a : Fin (Module.finrank F ((V d ⧸ A) ⧸ L) + 1) → F) :
    a ∈ Q.domainFixed.map (lineAdaptedEquiv L hL).toLinearMap ↔
      (lineAdaptedEquiv L hL).symm a ∈ Q.domainFixed := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro ha
    exact ⟨(lineAdaptedEquiv L hL).symm a, ha,
      (lineAdaptedEquiv L hL).apply_symm_apply a⟩

private theorem mem_line_codomain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (Q : CarrierRestriction A B)
    (b : Fin (Module.finrank F B) → F) :
    b ∈ Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap ↔
      (codomainBasis B).equivFun.symm b ∈ Q.codomainVariation := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hb
    exact ⟨(codomainBasis B).equivFun.symm b, hb,
      (codomainBasis B).equivFun.apply_symm_apply b⟩

theorem mem_line_coordinate_fibre_iff {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B) (M : (V d ⧸ A) →ₗ[F] B) :
    lineMatrixEquiv B L hL M ∈ (lineCoordinateRestriction L hL Q).fibre ↔
      M ∈ Q.fibre := by
  simp only [ActualAffineRestriction.fibre, CarrierRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      have h := hD (lineAdaptedEquiv L hL u) ⟨u, hu, rfl⟩
      have hm : (codomainBasis B).equivFun ((M - Q.base) u) = 0 := by
        simpa only [lineCoordinateRestriction, lineMatrix_sub_mulVec] using h
      exact (codomainBasis B).equivFun.injective (by simpa using hm)
    · intro u
      have h := hC (lineAdaptedEquiv L hL u)
      have hm : (codomainBasis B).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap := by
        simpa only [lineCoordinateRestriction, lineMatrix_sub_mulVec] using h
      have hh := (mem_line_codomain_coordinates Q _).mp hm
      simpa only [LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      let u := (lineAdaptedEquiv L hL).symm a
      have hu : u ∈ Q.domainFixed :=
        (mem_line_domain_coordinates L hL Q a).mp ha
      have hm := lineMatrix_sub_mulVec B L hL M Q.base u
      have h0 := hD u hu
      have ha' : lineAdaptedEquiv L hL u = a :=
        (lineAdaptedEquiv L hL).apply_symm_apply a
      simpa [lineCoordinateRestriction, ha', h0] using hm
    · intro a
      let u := (lineAdaptedEquiv L hL).symm a
      have hu := hC u
      have ha' : lineAdaptedEquiv L hL u = a :=
        (lineAdaptedEquiv L hL).apply_symm_apply a
      have hh : (codomainBasis B).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap :=
        (mem_line_codomain_coordinates Q _).mpr
          (by simpa only [LinearEquiv.symm_apply_apply] using hu)
      change (lineMatrixEquiv B L hL M -
        lineMatrixEquiv B L hL Q.base).mulVec a ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap
      rw [← ha', lineMatrix_sub_mulVec]
      exact hh

theorem line_coordinate_fibre_image {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B) :
    (lineCoordinateRestriction L hL Q).fibre =
      Q.fibre.image (lineMatrixEquiv B L hL) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨(lineMatrixEquiv B L hL).symm X, ?_, by simp⟩
    exact (mem_line_coordinate_fibre_iff L hL Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (mem_line_coordinate_fibre_iff L hL Q M).mpr hM

theorem line_coordinate_fibre_energy {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    fibreEnergy (lineCoordinateRestriction L hL Q).fibre
        (fun X => f ((lineMatrixEquiv B L hL).symm X)) =
      (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [line_coordinate_fibre_image]
  have hi : Set.InjOn (lineMatrixEquiv B L hL :
      ((V d ⧸ A) →ₗ[F] B) → BinaryMatrix
        (Module.finrank F B) (Module.finrank F ((V d ⧸ A) ⧸ L) + 1)) Q.fibre :=
    (lineMatrixEquiv B L hL).injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, LinearEquiv.symm_apply_apply]

theorem line_coordinate_order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (Q : CarrierRestriction A B) :
    (lineCoordinateRestriction L hL Q).order = Q.order := by
  let eU := lineAdaptedEquiv L hL
  let eZ := (codomainBasis B).equivFun
  have hU : Module.finrank F (Q.domainFixed.map eU.toLinearMap) =
      Module.finrank F Q.domainFixed := eU.finrank_map_eq Q.domainFixed
  have hZ : Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
      Module.finrank F Q.codomainVariation :=
    eZ.finrank_map_eq Q.codomainVariation
  have hTot : Module.finrank F (Fin (Module.finrank F B) → F) =
      Module.finrank F B := eZ.finrank_eq.symm
  have hCoord :=
    (Q.codomainVariation.map eZ.toLinearMap).finrank_quotient_add_finrank
  have hTyped := Q.codomainVariation.finrank_quotient_add_finrank
  have hCoord' : Module.finrank F
      ((Fin (Module.finrank F B) → F) ⧸
        Q.codomainVariation.map eZ.toLinearMap) +
      Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
        Module.finrank F (Fin (Module.finrank F B) → F) := hCoord
  have hTyped' : Module.finrank F (B ⧸ Q.codomainVariation) +
      Module.finrank F Q.codomainVariation = Module.finrank F B := hTyped
  change Module.finrank F (Q.domainFixed.map eU.toLinearMap) +
      Module.finrank F
        ((Fin (Module.finrank F B) → F) ⧸
          Q.codomainVariation.map eZ.toLinearMap) =
    Module.finrank F Q.domainFixed +
      Module.finrank F (B ⧸ Q.codomainVariation)
  rw [hU]
  clear hCoord hTyped
  omega

def lineTypedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (R : ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L) + 1)) : CarrierRestriction A B where
  domainFixed := R.domainFixed.map (lineAdaptedEquiv L hL).symm.toLinearMap
  codomainVariation :=
    R.codomainVariation.map (codomainBasis B).equivFun.symm.toLinearMap
  base := (lineMatrixEquiv B L hL).symm R.base

theorem line_coordinate_typedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (R : ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L) + 1)) :
    lineCoordinateRestriction L hL (lineTypedOfCoordinate A B L hL R) = R := by
  cases R with
  | mk D C T =>
    unfold lineTypedOfCoordinate lineCoordinateRestriction
    congr 1
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        change lineAdaptedEquiv L hL
          ((lineAdaptedEquiv L hL).symm w) ∈ D
        rw [(lineAdaptedEquiv L hL).apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(lineAdaptedEquiv L hL).symm u,
          ⟨u, hu, rfl⟩, (lineAdaptedEquiv L hL).apply_symm_apply u⟩
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        change (codomainBasis B).equivFun
          ((codomainBasis B).equivFun.symm w) ∈ C
        rw [(codomainBasis B).equivFun.apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(codomainBasis B).equivFun.symm u,
          ⟨u, hu, rfl⟩, (codomainBasis B).equivFun.apply_symm_apply u⟩
    · simp

theorem typed_global_iff_line_coordinate {n d r : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    UpToTypedNormSqGlobal A B r ε f ↔
      UpToActualNormSqGlobal r ε
        (fun X => f ((lineMatrixEquiv B L hL).symm X)) := by
  constructor
  · intro hf R hR
    let Q := lineTypedOfCoordinate A B L hL R
    have hQR : Q.order ≤ r := by
      rw [← line_coordinate_order L hL Q,
        line_coordinate_typedOfCoordinate]
      exact hR
    have h := hf Q hQR
    rw [← line_coordinate_fibre_energy L hL Q f,
      line_coordinate_typedOfCoordinate] at h
    exact h
  · intro hf Q hQ
    have h := hf (lineCoordinateRestriction L hL Q)
      (by rw [line_coordinate_order]; exact hQ)
    rw [line_coordinate_fibre_energy] at h
    exact h

/-- Coordinate presentation of the arbitrary typed line witness, at the
actual prescribed base, with the manuscript's exact one-step loss. -/
theorem typed_line_coordinate_witness_global {n d k : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A B (k + 1) ε f) :
    UpToActualNormSqGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun X => typedLineP B L hL k f
        ((lineMatrixEquiv B L hL).symm
          (rawLastColumn X (lineBaseColumn B L hL T)))) := by
  have hcoord :=
    (typed_global_iff_line_coordinate A B L hL f).mp hf
  have hw := actualGlobal_A15_complex_fixedLine
    (lineBaseColumn B L hL T)
    (fun X => f ((lineMatrixEquiv B L hL).symm X)) hε hcoord
  simpa only [typedLineP_coordinate, LinearEquiv.apply_symm_apply] using hw

theorem typed_line_coordinate_witness_fixed_base {n d k : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (N : ((V d ⧸ A) ⧸ L) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    typedLineP B L hL k f (T + N.comp L.mkQ) =
      typedLineP B L hL k f
        ((lineMatrixEquiv B L hL).symm
          (rawLastColumn
            (dropLastMatrix (lineMatrixEquiv B L hL (T + N.comp L.mkQ)))
            (lineBaseColumn B L hL T))) := by
  rw [← lineMatrix_rawLastColumn B L hL T N]
  simp

end
end PvNP.RealizableHardness.BinaryMatrixTypedA15AdaptedGlobal
