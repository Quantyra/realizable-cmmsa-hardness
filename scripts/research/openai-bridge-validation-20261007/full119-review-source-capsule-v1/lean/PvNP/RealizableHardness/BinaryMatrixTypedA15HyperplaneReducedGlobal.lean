import PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReduced
import PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReducedGlobal

open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15Hyperplane
open BinaryMatrixTypedA15HyperplaneReduced BinaryMatrixTypedA15HyperplaneGlobal
  BinaryMatrixFourier
open BinaryMatrixActualAffine BinaryMatrixComplexA15
open BinaryMatrixCodomainA15 BinaryMatrixTypedA15ReducedGlobal
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

structure HyperplaneReducedRestriction {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) where
  domainFixed : Submodule F (V d ⧸ A)
  codomainVariation : Submodule F H
  base : (V d ⧸ A) →ₗ[F] H

def HyperplaneReducedRestriction.order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {H : Submodule F B} (Q : HyperplaneReducedRestriction A B H) : ℕ :=
  Module.finrank F Q.domainFixed + Module.finrank F (H ⧸ Q.codomainVariation)

private noncomputable instance reducedFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) : Fintype ((V d ⧸ A) →ₗ[F] H) := by
  letI : Fintype (V d ⧸ A) := Fintype.ofFinite _
  letI : Fintype H := Fintype.ofFinite _
  exact FunLike.fintype _

def HyperplaneReducedRestriction.fibre {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {H : Submodule F B} (Q : HyperplaneReducedRestriction A B H) :
    Finset ((V d ⧸ A) →ₗ[F] H) :=
  Finset.univ.filter (fun M =>
    (∀ a ∈ Q.domainFixed, (M - Q.base) a = 0) ∧
    (∀ v : V d ⧸ A, (M - Q.base) v ∈ Q.codomainVariation))

def UpToHyperplaneReducedNormSqGlobal {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (r : ℕ) (ε : ℝ)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ) : Prop :=
  ∀ Q : HyperplaneReducedRestriction A B H, Q.order ≤ r →
    (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card ≤ ε

def reducedCoordinateRestriction {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H) :
    ActualAffineRestriction (Module.finrank F H)
      (Module.finrank F (V d ⧸ A)) where
  domainFixed := Q.domainFixed.map ((domainBasis A).equivFun).toLinearMap
  codomainVariation := Q.codomainVariation.map ((Module.finBasis F H).equivFun).toLinearMap
  base := hyperplaneReducedMatrixEquiv H Q.base

theorem reducedMatrix_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M : (V d ⧸ A) →ₗ[F] H) (u : V d ⧸ A) :
    (hyperplaneReducedMatrixEquiv H M).mulVec ((domainBasis A).equivFun u) =
      (Module.finBasis F H).equivFun (M u) := by
  change (LinearMap.toMatrix (domainBasis A) (Module.finBasis F H) M).mulVec
      ((domainBasis A).repr u) = (Module.finBasis F H).repr (M u)
  exact LinearMap.toMatrix_mulVec_repr (domainBasis A) (Module.finBasis F H) M u

theorem reducedMatrix_sub_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (M T : (V d ⧸ A) →ₗ[F] H) (u : V d ⧸ A) :
    (hyperplaneReducedMatrixEquiv H M - hyperplaneReducedMatrixEquiv H T).mulVec
        ((domainBasis A).equivFun u) =
      (Module.finBasis F H).equivFun ((M - T) u) := by
  rw [← map_sub]
  exact reducedMatrix_mulVec B H hH (M - T) u

private theorem mem_reduced_domain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H)
    (a : Fin (Module.finrank F (V d ⧸ A)) → F) :
    a ∈ Q.domainFixed.map ((domainBasis A).equivFun).toLinearMap ↔
      (domainBasis A).equivFun.symm a ∈ Q.domainFixed := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro ha
    exact ⟨(domainBasis A).equivFun.symm a, ha,
      (domainBasis A).equivFun.apply_symm_apply a⟩

private theorem mem_reduced_codomain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H)
    (b : Fin (Module.finrank F H) → F) :
    b ∈ Q.codomainVariation.map ((Module.finBasis F H).equivFun).toLinearMap ↔
      (Module.finBasis F H).equivFun.symm b ∈ Q.codomainVariation := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hb
    exact ⟨(Module.finBasis F H).equivFun.symm b, hb,
      (Module.finBasis F H).equivFun.apply_symm_apply b⟩

theorem mem_reduced_coordinate_fibre_iff {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H) (M : (V d ⧸ A) →ₗ[F] H) :
    hyperplaneReducedMatrixEquiv H M ∈ (reducedCoordinateRestriction H hH Q).fibre ↔
      M ∈ Q.fibre := by
  simp only [ActualAffineRestriction.fibre, HyperplaneReducedRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      have h := hD ((domainBasis A).equivFun u) ⟨u, hu, rfl⟩
      have hm : (Module.finBasis F H).equivFun ((M - Q.base) u) = 0 := by
        change (hyperplaneReducedMatrixEquiv H M -
          hyperplaneReducedMatrixEquiv H Q.base).mulVec
            ((domainBasis A).equivFun u) = 0 at h
        rwa [reducedMatrix_sub_mulVec B H hH] at h
      exact (Module.finBasis F H).equivFun.injective (by simpa using hm)
    · intro u
      have h := hC ((domainBasis A).equivFun u)
      have hm : (Module.finBasis F H).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map ((Module.finBasis F H).equivFun).toLinearMap := by
        change (hyperplaneReducedMatrixEquiv H M -
          hyperplaneReducedMatrixEquiv H Q.base).mulVec
            ((domainBasis A).equivFun u) ∈
              Q.codomainVariation.map ((Module.finBasis F H).equivFun).toLinearMap at h
        rwa [reducedMatrix_sub_mulVec B H hH] at h
      have hh := (mem_reduced_codomain_coordinates H hH Q _).mp hm
      simpa only [LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      let u := (domainBasis A).equivFun.symm a
      have hu : u ∈ Q.domainFixed :=
        (mem_reduced_domain_coordinates H hH Q a).mp ha
      have hm := reducedMatrix_sub_mulVec B H hH M Q.base u
      have h0 := hD u hu
      have ha' : (domainBasis A).equivFun u = a :=
        (domainBasis A).equivFun.apply_symm_apply a
      change (hyperplaneReducedMatrixEquiv H M -
        hyperplaneReducedMatrixEquiv H Q.base).mulVec a = 0
      rw [← ha', reducedMatrix_sub_mulVec B H hH, h0]
      simp
    · intro a
      let u := (domainBasis A).equivFun.symm a
      have hu := hC u
      have ha' : (domainBasis A).equivFun u = a :=
        (domainBasis A).equivFun.apply_symm_apply a
      have hh : (Module.finBasis F H).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map ((Module.finBasis F H).equivFun).toLinearMap :=
        (mem_reduced_codomain_coordinates H hH Q _).mpr
          (by simpa only [LinearEquiv.symm_apply_apply] using hu)
      change (hyperplaneReducedMatrixEquiv H M -
        hyperplaneReducedMatrixEquiv H Q.base).mulVec a ∈
          Q.codomainVariation.map ((Module.finBasis F H).equivFun).toLinearMap
      rw [← ha', reducedMatrix_sub_mulVec B H hH]
      exact hh

theorem reduced_coordinate_fibre_image {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H) :
    (reducedCoordinateRestriction H hH Q).fibre =
      Q.fibre.image (hyperplaneReducedMatrixEquiv H) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨(hyperplaneReducedMatrixEquiv H).symm X, ?_, by simp⟩
    exact (mem_reduced_coordinate_fibre_iff H hH Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (mem_reduced_coordinate_fibre_iff H hH Q M).mpr hM

theorem reduced_coordinate_fibre_energy {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ) :
    fibreEnergy (reducedCoordinateRestriction H hH Q).fibre
        (fun X => f ((hyperplaneReducedMatrixEquiv H).symm X)) =
      (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [reduced_coordinate_fibre_image]
  have hi : Set.InjOn (hyperplaneReducedMatrixEquiv H :
      ((V d ⧸ A) →ₗ[F] H) → BinaryMatrix
        (Module.finrank F H) (Module.finrank F (V d ⧸ A))) Q.fibre :=
    (hyperplaneReducedMatrixEquiv H).injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, LinearEquiv.symm_apply_apply]

theorem reduced_coordinate_order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (Q : HyperplaneReducedRestriction A B H) :
    (reducedCoordinateRestriction H hH Q).order = Q.order := by
  let eU := (domainBasis A).equivFun
  let eZ := (Module.finBasis F H).equivFun
  have hU : Module.finrank F (Q.domainFixed.map eU.toLinearMap) =
      Module.finrank F Q.domainFixed := eU.finrank_map_eq Q.domainFixed
  have hZ : Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
      Module.finrank F Q.codomainVariation :=
    eZ.finrank_map_eq Q.codomainVariation
  have hTot : Module.finrank F (Fin (Module.finrank F H) → F) =
      Module.finrank F H := eZ.finrank_eq.symm
  have hCoord :=
    (Q.codomainVariation.map eZ.toLinearMap).finrank_quotient_add_finrank
  have hTyped := Q.codomainVariation.finrank_quotient_add_finrank
  have hCoord' : Module.finrank F
      ((Fin (Module.finrank F H) → F) ⧸
        Q.codomainVariation.map eZ.toLinearMap) +
      Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
        Module.finrank F (Fin (Module.finrank F H) → F) := hCoord
  have hTyped' : Module.finrank F (H ⧸ Q.codomainVariation) +
      Module.finrank F Q.codomainVariation = Module.finrank F H := hTyped
  change Module.finrank F (Q.domainFixed.map eU.toLinearMap) +
      Module.finrank F
        ((Fin (Module.finrank F H) → F) ⧸
          Q.codomainVariation.map eZ.toLinearMap) =
    Module.finrank F Q.domainFixed +
      Module.finrank F (H ⧸ Q.codomainVariation)
  rw [hU]
  clear hCoord hTyped
  omega

def reducedTypedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (R : ActualAffineRestriction (Module.finrank F H)
      (Module.finrank F (V d ⧸ A))) : HyperplaneReducedRestriction A B H where
  domainFixed := R.domainFixed.map ((domainBasis A).equivFun.symm).toLinearMap
  codomainVariation :=
    R.codomainVariation.map ((Module.finBasis F H).equivFun.symm).toLinearMap
  base := (hyperplaneReducedMatrixEquiv H).symm R.base

theorem reduced_coordinate_typedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (R : ActualAffineRestriction (Module.finrank F H)
      (Module.finrank F (V d ⧸ A))) :
    reducedCoordinateRestriction H hH (reducedTypedOfCoordinate A B H hH R) = R := by
  cases R with
  | mk D C T =>
    unfold reducedTypedOfCoordinate reducedCoordinateRestriction
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
        change (Module.finBasis F H).equivFun
          ((Module.finBasis F H).equivFun.symm w) ∈ C
        rw [(Module.finBasis F H).equivFun.apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(Module.finBasis F H).equivFun.symm u,
          ⟨u, hu, rfl⟩, (Module.finBasis F H).equivFun.apply_symm_apply u⟩
    · simp

theorem reduced_global_iff_coordinate {n d r : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ) :
    UpToHyperplaneReducedNormSqGlobal A B H r ε f ↔
      UpToActualNormSqGlobal r ε
        (fun X => f ((hyperplaneReducedMatrixEquiv H).symm X)) := by
  constructor
  · intro hf R hR
    let Q := reducedTypedOfCoordinate A B H hH R
    have hQR : Q.order ≤ r := by
      rw [← reduced_coordinate_order H hH Q,
        reduced_coordinate_typedOfCoordinate]
      exact hR
    have h := hf Q hQR
    rw [← reduced_coordinate_fibre_energy H hH Q f,
      reduced_coordinate_typedOfCoordinate] at h
    exact h
  · intro hf Q hQ
    have h := hf (reducedCoordinateRestriction H hH Q)
      (by rw [reduced_coordinate_order]; exact hQ)
    rw [reduced_coordinate_fibre_energy] at h
    exact h

def typedHyperplaneReducedWitness {n d k : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    ((V d ⧸ A) →ₗ[F] H) → ℂ :=
  fun N => typedHyperplaneP B H hH k f (T + H.subtype.comp N)

theorem hyperplane_witness_coordinate_shift {n d k : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (X : BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ A))) :
    typedHyperplaneReducedWitness (k := k) B H hH T f
      ((hyperplaneReducedMatrixEquiv H).symm X) =
    typedHyperplaneP B H hH k f
      ((hyperplaneMatrixEquiv B H hH).symm
        (rawLastRow
          (X + dropLastRow (hyperplaneMatrixEquiv B H hH T))
          (hyperplaneBaseRow B H hH T))) := by
  let N := (hyperplaneReducedMatrixEquiv H).symm X
  have hw := typed_hyperplane_coordinate_witness_fixed_base
    (k := k) B H hH T N f
  rw [dropLastRow_hyperplaneMatrix_fixed_base] at hw
  have hN : hyperplaneReducedMatrixEquiv H N = X :=
    (hyperplaneReducedMatrixEquiv H).apply_symm_apply X
  rw [hN] at hw
  rw [add_comm (dropLastRow (hyperplaneMatrixEquiv B H hH T)) X] at hw
  exact hw

theorem hyperplane_witness_coordinate_shift_complex {n d k : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (X : BinaryMatrix (Module.finrank F H) (Module.finrank F (V d ⧸ A))) :
    typedHyperplaneReducedWitness (k := k) B H hH T f
      ((hyperplaneReducedMatrixEquiv H).symm X) =
    complexHyperplaneP k
      (fun Z => f ((hyperplaneMatrixEquiv B H hH).symm Z))
      (rawLastRow
        (X + dropLastRow (hyperplaneMatrixEquiv B H hH T))
        (hyperplaneBaseRow B H hH T)) := by
  calc
    _ = typedHyperplaneP B H hH k f
      ((hyperplaneMatrixEquiv B H hH).symm
        (rawLastRow
          (X + dropLastRow (hyperplaneMatrixEquiv B H hH T))
          (hyperplaneBaseRow B H hH T))) :=
        hyperplane_witness_coordinate_shift B H hH T f X
    _ = _ := by
      simp only [typedHyperplaneP,
        LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 800000 in
theorem typed_hyperplane_oneStep_A15_global {n d k : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A B (k + 1) ε f) :
    UpToHyperplaneReducedNormSqGlobal A B H k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (typedHyperplaneReducedWitness (k := k) B H hH T f) := by
  let G : BinaryMatrix (Module.finrank F H)
      (Module.finrank F (V d ⧸ A)) → ℂ :=
    fun X => typedHyperplaneP B H hH k f
      ((hyperplaneMatrixEquiv B H hH).symm
        (rawLastRow X (hyperplaneBaseRow B H hH T)))
  let c := dropLastRow (hyperplaneMatrixEquiv B H hH T)
  have hG : UpToActualNormSqGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε) G :=
    typed_hyperplane_coordinate_witness_global A B H hH T f hε hf
  have hδ : 0 ≤ 4 * (2 : ℝ) ^ (4 * (k + 1)) * ε := by positivity
  have htr := translate_actual_complex c G hδ hG
  apply (reduced_global_iff_coordinate A B H hH
    (typedHyperplaneReducedWitness (k := k) B H hH T f)).mpr
  have heq : (fun X => typedHyperplaneReducedWitness (k := k) B H hH T f
      ((hyperplaneReducedMatrixEquiv H).symm X)) =
      (fun X => G (X + c)) := by
    funext X
    exact hyperplane_witness_coordinate_shift B H hH T f X
  rw [heq]
  exact htr


end
end PvNP.RealizableHardness.BinaryMatrixTypedA15HyperplaneReducedGlobal
