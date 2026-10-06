import PvNP.RealizableHardness.BinaryMatrixTypedA15Hyperplane

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneGlobal

open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15OneStep BinaryMatrixTypedA15Hyperplane BinaryMatrixFourier
open BinaryMatrixFirstDerivative
open BinaryMatrixLineA15
open BinaryMatrixActualAffine BinaryMatrixComplexA15
open BinaryMatrixCodomainA15
set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

def hyperplaneCoordinateRestriction {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B) :
    ActualAffineRestriction (Module.finrank F H + 1)
      (Module.finrank F (V d ⧸ A)) where
  domainFixed := Q.domainFixed.map ((domainBasis A).equivFun).toLinearMap
  codomainVariation := Q.codomainVariation.map (hyperplaneAdaptedEquiv B H hH).toLinearMap
  base := hyperplaneMatrixEquiv B H hH Q.base

theorem hyperplaneMatrix_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M : (V d ⧸ A) →ₗ[F] B) (u : V d ⧸ A) :
    (hyperplaneMatrixEquiv B H hH M).mulVec ((domainBasis A).equivFun u) =
      (hyperplaneAdaptedEquiv B H hH) (M u) := by
  simp only [hyperplaneMatrixEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem hyperplaneMatrix_sub_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M T : (V d ⧸ A) →ₗ[F] B) (u : V d ⧸ A) :
    (hyperplaneMatrixEquiv B H hH M - hyperplaneMatrixEquiv B H hH T).mulVec
        ((domainBasis A).equivFun u) =
      (hyperplaneAdaptedEquiv B H hH) ((M - T) u) := by
  rw [← map_sub]
  exact hyperplaneMatrix_mulVec B H hH (M - T) u

private theorem mem_hyperplane_domain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B)
    (a : Fin (Module.finrank F (V d ⧸ A)) → F) :
    a ∈ Q.domainFixed.map ((domainBasis A).equivFun).toLinearMap ↔
      (domainBasis A).equivFun.symm a ∈ Q.domainFixed := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro ha
    exact ⟨(domainBasis A).equivFun.symm a, ha,
      (domainBasis A).equivFun.apply_symm_apply a⟩

private theorem mem_hyperplane_codomain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B)
    (b : Fin (Module.finrank F H + 1) → F) :
    b ∈ Q.codomainVariation.map (hyperplaneAdaptedEquiv B H hH).toLinearMap ↔
      (hyperplaneAdaptedEquiv B H hH).symm b ∈ Q.codomainVariation := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hb
    exact ⟨(hyperplaneAdaptedEquiv B H hH).symm b, hb,
      (hyperplaneAdaptedEquiv B H hH).apply_symm_apply b⟩

theorem mem_hyperplane_coordinate_fibre_iff {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B) (M : (V d ⧸ A) →ₗ[F] B) :
    hyperplaneMatrixEquiv B H hH M ∈ (hyperplaneCoordinateRestriction H hH Q).fibre ↔
      M ∈ Q.fibre := by
  simp only [ActualAffineRestriction.fibre, CarrierRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      have h := hD ((domainBasis A).equivFun u) ⟨u, hu, rfl⟩
      have hm : (hyperplaneAdaptedEquiv B H hH) ((M - Q.base) u) = 0 := by
        simpa only [hyperplaneCoordinateRestriction, hyperplaneMatrix_sub_mulVec] using h
      exact (hyperplaneAdaptedEquiv B H hH).injective (by simpa using hm)
    · intro u
      have h := hC ((domainBasis A).equivFun u)
      have hm : (hyperplaneAdaptedEquiv B H hH) ((M - Q.base) u) ∈
          Q.codomainVariation.map (hyperplaneAdaptedEquiv B H hH).toLinearMap := by
        simpa only [hyperplaneCoordinateRestriction, hyperplaneMatrix_sub_mulVec] using h
      have hh := (mem_hyperplane_codomain_coordinates H hH Q _).mp hm
      simpa only [LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      let u := (domainBasis A).equivFun.symm a
      have hu : u ∈ Q.domainFixed :=
        (mem_hyperplane_domain_coordinates H hH Q a).mp ha
      have hm := hyperplaneMatrix_sub_mulVec B H hH M Q.base u
      have h0 := hD u hu
      have ha' : (domainBasis A).equivFun u = a :=
        (domainBasis A).equivFun.apply_symm_apply a
      simpa [hyperplaneCoordinateRestriction, ha', h0] using hm
    · intro a
      let u := (domainBasis A).equivFun.symm a
      have hu := hC u
      have ha' : (domainBasis A).equivFun u = a :=
        (domainBasis A).equivFun.apply_symm_apply a
      have hh : (hyperplaneAdaptedEquiv B H hH) ((M - Q.base) u) ∈
          Q.codomainVariation.map (hyperplaneAdaptedEquiv B H hH).toLinearMap :=
        (mem_hyperplane_codomain_coordinates H hH Q _).mpr
          (by simpa only [LinearEquiv.symm_apply_apply] using hu)
      change (hyperplaneMatrixEquiv B H hH M -
        hyperplaneMatrixEquiv B H hH Q.base).mulVec a ∈
          Q.codomainVariation.map (hyperplaneAdaptedEquiv B H hH).toLinearMap
      rw [← ha', hyperplaneMatrix_sub_mulVec]
      exact hh

theorem hyperplane_coordinate_fibre_image {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B) :
    (hyperplaneCoordinateRestriction H hH Q).fibre =
      Q.fibre.image (hyperplaneMatrixEquiv B H hH) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨(hyperplaneMatrixEquiv B H hH).symm X, ?_, by simp⟩
    exact (mem_hyperplane_coordinate_fibre_iff H hH Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (mem_hyperplane_coordinate_fibre_iff H hH Q M).mpr hM

theorem hyperplane_coordinate_fibre_energy {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    fibreEnergy (hyperplaneCoordinateRestriction H hH Q).fibre
        (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X)) =
      (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [hyperplane_coordinate_fibre_image]
  have hi : Set.InjOn (hyperplaneMatrixEquiv B H hH :
      ((V d ⧸ A) →ₗ[F] B) → BinaryMatrix
        (Module.finrank F H + 1) (Module.finrank F (V d ⧸ A))) Q.fibre :=
    (hyperplaneMatrixEquiv B H hH).injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, LinearEquiv.symm_apply_apply]

theorem hyperplane_coordinate_order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : CarrierRestriction A B) :
    (hyperplaneCoordinateRestriction H hH Q).order = Q.order := by
  let eU := (domainBasis A).equivFun
  let eZ := (hyperplaneAdaptedEquiv B H hH)
  have hU : Module.finrank F (Q.domainFixed.map eU.toLinearMap) =
      Module.finrank F Q.domainFixed := eU.finrank_map_eq Q.domainFixed
  have hZ : Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
      Module.finrank F Q.codomainVariation :=
    eZ.finrank_map_eq Q.codomainVariation
  have hTot : Module.finrank F (Fin (Module.finrank F H + 1) → F) =
      Module.finrank F B := eZ.finrank_eq.symm
  have hCoord :=
    (Q.codomainVariation.map eZ.toLinearMap).finrank_quotient_add_finrank
  have hTyped := Q.codomainVariation.finrank_quotient_add_finrank
  have hCoord' : Module.finrank F
      ((Fin (Module.finrank F H + 1) → F) ⧸
        Q.codomainVariation.map eZ.toLinearMap) +
      Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
        Module.finrank F (Fin (Module.finrank F H + 1) → F) := hCoord
  have hTyped' : Module.finrank F (B ⧸ Q.codomainVariation) +
      Module.finrank F Q.codomainVariation = Module.finrank F B := hTyped
  change Module.finrank F (Q.domainFixed.map eU.toLinearMap) +
      Module.finrank F
        ((Fin (Module.finrank F H + 1) → F) ⧸
          Q.codomainVariation.map eZ.toLinearMap) =
    Module.finrank F Q.domainFixed +
      Module.finrank F (B ⧸ Q.codomainVariation)
  rw [hU]
  clear hCoord hTyped
  omega

def hyperplaneTypedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (R : ActualAffineRestriction (Module.finrank F H + 1)
      (Module.finrank F (V d ⧸ A))) : CarrierRestriction A B where
  domainFixed := R.domainFixed.map ((domainBasis A).equivFun.symm).toLinearMap
  codomainVariation :=
    R.codomainVariation.map (hyperplaneAdaptedEquiv B H hH).symm.toLinearMap
  base := (hyperplaneMatrixEquiv B H hH).symm R.base

theorem hyperplane_coordinate_typedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (R : ActualAffineRestriction (Module.finrank F H + 1)
      (Module.finrank F (V d ⧸ A))) :
    hyperplaneCoordinateRestriction H hH (hyperplaneTypedOfCoordinate A B H hH R) = R := by
  cases R with
  | mk D C T =>
    unfold hyperplaneTypedOfCoordinate hyperplaneCoordinateRestriction
    congr 1
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        change (domainBasis A).equivFun
          ((domainBasis A).equivFun.symm w) ∈ D
        rw [(domainBasis A).equivFun.apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(domainBasis A).equivFun.symm u,
          ⟨u, hu, rfl⟩, (domainBasis A).equivFun.apply_symm_apply u⟩
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        change (hyperplaneAdaptedEquiv B H hH)
          ((hyperplaneAdaptedEquiv B H hH).symm w) ∈ C
        rw [(hyperplaneAdaptedEquiv B H hH).apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(hyperplaneAdaptedEquiv B H hH).symm u,
          ⟨u, hu, rfl⟩, (hyperplaneAdaptedEquiv B H hH).apply_symm_apply u⟩
    · simp

theorem typed_global_iff_hyperplane_coordinate {n d r : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    UpToTypedNormSqGlobal A B r ε f ↔
      UpToActualNormSqGlobal r ε
        (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X)) := by
  constructor
  · intro hf R hR
    let Q := hyperplaneTypedOfCoordinate A B H hH R
    have hQR : Q.order ≤ r := by
      rw [← hyperplane_coordinate_order H hH Q,
        hyperplane_coordinate_typedOfCoordinate]
      exact hR
    have h := hf Q hQR
    rw [← hyperplane_coordinate_fibre_energy H hH Q f,
      hyperplane_coordinate_typedOfCoordinate] at h
    exact h
  · intro hf Q hQ
    have h := hf (hyperplaneCoordinateRestriction H hH Q)
      (by rw [hyperplane_coordinate_order]; exact hQ)
    rw [hyperplane_coordinate_fibre_energy] at h
    exact h

/-- Intrinsic presentation of the actual complex codomain-hyperplane
translation polynomial, with one adapted codomain basis fixed throughout. -/
def typedHyperplaneP {n d : ℕ} {A : Submodule F (V d)}
    (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (k : ℕ) (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    ((V d ⧸ A) →ₗ[F] B) → ℂ :=
  fun M => complexHyperplaneP k
    (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X))
      (hyperplaneMatrixEquiv B H hH M)

set_option maxHeartbeats 600000 in
theorem typed_hyperplane_coordinate_witness_global {n d k : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A B (k + 1) ε f) :
    UpToActualNormSqGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun X => typedHyperplaneP B H hH k f
        ((hyperplaneMatrixEquiv B H hH).symm
          (rawLastRow X (hyperplaneBaseRow B H hH T)))) := by
  have hcoord := (typed_global_iff_hyperplane_coordinate A B H hH f).mp hf
  have hw := actualGlobal_A15_complex_fixedHyperplane
    (hyperplaneBaseRow B H hH T)
    (fun X => f ((hyperplaneMatrixEquiv B H hH).symm X)) hε hcoord
  simpa only [typedHyperplaneP, LinearEquiv.apply_symm_apply] using hw

theorem typed_hyperplane_coordinate_witness_fixed_base {n d k : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B) (N : (V d ⧸ A) →ₗ[F] H)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    typedHyperplaneP B H hH k f (T + H.subtype.comp N) =
      typedHyperplaneP B H hH k f
        ((hyperplaneMatrixEquiv B H hH).symm
          (rawLastRow
            (dropLastRow (hyperplaneMatrixEquiv B H hH (T + H.subtype.comp N)))
            (hyperplaneBaseRow B H hH T))) := by
  rw [← hyperplaneMatrix_rawLastRow B H hH T N]
  simp


end
end PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneGlobal
