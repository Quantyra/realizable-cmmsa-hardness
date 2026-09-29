import PvNP.RealizableHardness.BinaryMatrixComplexA14

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15Transport

open BinaryMatrixFourier BinaryMatrixActualAffine BinaryMatrixComplexA15
open scoped BigOperators
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def domainBasis {d : ℕ} (A : Submodule F (V d)) :=
  Module.finBasis F (V d ⧸ A)

def codomainBasis {n : ℕ} (B : Submodule F (W n)) :=
  Module.finBasis F B

def carrierMatrixEquiv {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    ((V d ⧸ A) →ₗ[F] B) ≃ₗ[F]
      BinaryMatrix (Module.finrank F B) (Module.finrank F (V d ⧸ A)) :=
  LinearMap.toMatrix (domainBasis A) (codomainBasis B)

/-- The typed actual affine restriction of the A1 carrier, whose base is
the specified linear map on the quotient/subtype. -/
structure CarrierRestriction {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) where
  domainFixed : Submodule F (V d ⧸ A)
  codomainVariation : Submodule F B
  base : (V d ⧸ A) →ₗ[F] B

def CarrierRestriction.order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B) : ℕ :=
  Module.finrank F Q.domainFixed + Module.finrank F (B ⧸ Q.codomainVariation)

private noncomputable instance carrierFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n)) :
    Fintype ((V d ⧸ A) →ₗ[F] B) := by
  classical
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

def CarrierRestriction.fibre {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B) : Finset ((V d ⧸ A) →ₗ[F] B) :=
  Finset.univ.filter (fun M =>
    (∀ a ∈ Q.domainFixed, (M - Q.base) a = 0) ∧
    (∀ v : V d ⧸ A, (M - Q.base) v ∈ Q.codomainVariation))

/-- Basis coordinates of a typed actual affine restriction. Both basis
choices are fixed once by the A1 carrier and reused for its base. -/
def coordinateRestriction {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B) :
    ActualAffineRestriction (Module.finrank F B) (Module.finrank F (V d ⧸ A)) where
  domainFixed := Q.domainFixed.map (domainBasis A).equivFun.toLinearMap
  codomainVariation := Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap
  base := carrierMatrixEquiv A B Q.base

theorem carrierMatrix_mulVec {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M : (V d ⧸ A) →ₗ[F] B) (u : V d ⧸ A) :
    (carrierMatrixEquiv A B M).mulVec ((domainBasis A).equivFun u) =
      (codomainBasis B).equivFun (M u) := by
  exact LinearMap.toMatrix_mulVec_repr (domainBasis A) (codomainBasis B) M u

theorem carrierMatrix_sub_mulVec {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (M T : (V d ⧸ A) →ₗ[F] B) (u : V d ⧸ A) :
    ((carrierMatrixEquiv A B M) - (carrierMatrixEquiv A B T)).mulVec
        ((domainBasis A).equivFun u) =
      (codomainBasis B).equivFun ((M - T) u) := by
  rw [← map_sub]
  exact carrierMatrix_mulVec A B (M - T) u

private theorem mem_domain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B)
    (a : Fin (Module.finrank F (V d ⧸ A)) → F) :
    a ∈ Q.domainFixed.map (domainBasis A).equivFun.toLinearMap ↔
      (domainBasis A).equivFun.symm a ∈ Q.domainFixed := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro ha
    exact ⟨(domainBasis A).equivFun.symm a, ha,
      (domainBasis A).equivFun.apply_symm_apply a⟩

private theorem mem_codomain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
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

/-- Coordinate fibres are precisely images of the same-base typed fibres.
This is the pointwise comparison needed to transport the A15 premise. -/
theorem mem_coordinate_fibre_iff {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B) (M : (V d ⧸ A) →ₗ[F] B) :
    carrierMatrixEquiv A B M ∈ (coordinateRestriction Q).fibre ↔
      M ∈ Q.fibre := by
  simp only [ActualAffineRestriction.fibre, CarrierRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      have h := hD ((domainBasis A).equivFun u)
        (by exact ⟨u, hu, rfl⟩)
      have hm : (codomainBasis B).equivFun ((M - Q.base) u) = 0 := by
        simpa only [coordinateRestriction, carrierMatrix_sub_mulVec] using h
      exact (codomainBasis B).equivFun.injective (by simpa using hm)
    · intro u
      have h := hC ((domainBasis A).equivFun u)
      have hm : (codomainBasis B).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap := by
        simpa only [coordinateRestriction, carrierMatrix_sub_mulVec] using h
      have hh := (mem_codomain_coordinates Q _).mp hm
      simpa only [LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      let u := (domainBasis A).equivFun.symm a
      have hu : u ∈ Q.domainFixed :=
        (mem_domain_coordinates Q a).mp ha
      have hm := carrierMatrix_sub_mulVec A B M Q.base u
      have h0 := hD u hu
      have ha' : (domainBasis A).equivFun u = a :=
        (domainBasis A).equivFun.apply_symm_apply a
      simpa [coordinateRestriction, ha', h0] using hm
    · intro a
      let u := (domainBasis A).equivFun.symm a
      have hu := hC u
      have hm := carrierMatrix_sub_mulVec A B M Q.base u
      have ha' : (domainBasis A).equivFun u = a :=
        (domainBasis A).equivFun.apply_symm_apply a
      have hh : (codomainBasis B).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap :=
        (mem_codomain_coordinates Q _).mpr
          (by simpa only [LinearEquiv.symm_apply_apply] using hu)
      change ((carrierMatrixEquiv A B M) -
        (carrierMatrixEquiv A B Q.base)).mulVec a ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap
      rw [← ha', carrierMatrix_sub_mulVec]
      exact hh

theorem coordinate_fibre_image {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B) :
    (coordinateRestriction Q).fibre =
      Q.fibre.image (carrierMatrixEquiv A B) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨(carrierMatrixEquiv A B).symm X, ?_, by simp⟩
    exact (mem_coordinate_fibre_iff Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (mem_coordinate_fibre_iff Q M).mpr hM

/-- The A15 normalized norm-square premise is invariant under the exact
coordinate fibre comparison, with no cardinality or base factor. -/
theorem coordinate_fibre_energy {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    fibreEnergy (coordinateRestriction Q).fibre
        (fun X => f ((carrierMatrixEquiv A B).symm X)) =
      (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [coordinate_fibre_image]
  have hi : Set.InjOn (carrierMatrixEquiv A B :
      ((V d ⧸ A) →ₗ[F] B) → BinaryMatrix
        (Module.finrank F B) (Module.finrank F (V d ⧸ A))) Q.fibre :=
    (carrierMatrixEquiv A B).injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, LinearEquiv.symm_apply_apply]

theorem coordinate_order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B) :
    (coordinateRestriction Q).order = Q.order := by
  let eU := (domainBasis A).equivFun
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
  change Module.finrank F (Q.domainFixed.map eU.toLinearMap) +
      Module.finrank F
        ((Fin (Module.finrank F B) → F) ⧸
          Q.codomainVariation.map eZ.toLinearMap) =
    Module.finrank F Q.domainFixed +
      Module.finrank F (B ⧸ Q.codomainVariation)
  rw [hU]
  omega

def typedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (R : ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F (V d ⧸ A))) : CarrierRestriction A B where
  domainFixed := R.domainFixed.map (domainBasis A).equivFun.symm.toLinearMap
  codomainVariation :=
    R.codomainVariation.map (codomainBasis B).equivFun.symm.toLinearMap
  base := (carrierMatrixEquiv A B).symm R.base

theorem coordinate_typedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (R : ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F (V d ⧸ A))) :
    coordinateRestriction (typedOfCoordinate A B R) = R := by
  cases R with
  | mk D C T =>
    unfold typedOfCoordinate coordinateRestriction
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
        change (codomainBasis B).equivFun
          ((codomainBasis B).equivFun.symm w) ∈ C
        rw [(codomainBasis B).equivFun.apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(codomainBasis B).equivFun.symm u,
          ⟨u, hu, rfl⟩, (codomainBasis B).equivFun.apply_symm_apply u⟩
    · simp

end
end PvNP.RealizableHardness.BinaryMatrixTypedA15Transport
