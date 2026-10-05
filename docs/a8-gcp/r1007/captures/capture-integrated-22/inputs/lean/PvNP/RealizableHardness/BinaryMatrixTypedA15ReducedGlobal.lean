import PvNP.RealizableHardness.BinaryMatrixTypedA15Reduced

namespace PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal

open BinaryMatrixTypedA15Reduced BinaryMatrixTypedA15OneStep
open BinaryMatrixTypedA15Transport BinaryMatrixTypedA15AdaptedGlobal
open BinaryMatrixFourier BinaryMatrixActualAffine BinaryMatrixComplexA15
open BinaryMatrixFirstDerivative BinaryMatrixLineA15
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F

structure ReducedRestriction {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) where
  domainFixed : Submodule F ((V d ⧸ A) ⧸ L)
  codomainVariation : Submodule F B
  base : ((V d ⧸ A) ⧸ L) →ₗ[F] B

def ReducedRestriction.order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L) : ℕ :=
  Module.finrank F Q.domainFixed + Module.finrank F (B ⧸ Q.codomainVariation)

private noncomputable instance reducedFintype {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) :
    Fintype (((V d ⧸ A) ⧸ L) →ₗ[F] B) := by
  classical
  letI : Fintype ((V d ⧸ A) ⧸ L) := Fintype.ofFinite _
  letI : Fintype B := Fintype.ofFinite _
  exact FunLike.fintype _

def ReducedRestriction.fibre {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L) :
    Finset (((V d ⧸ A) ⧸ L) →ₗ[F] B) :=
  Finset.univ.filter (fun M =>
    (∀ a ∈ Q.domainFixed, (M - Q.base) a = 0) ∧
    (∀ v : (V d ⧸ A) ⧸ L, (M - Q.base) v ∈ Q.codomainVariation))

def reducedCoordinateRestriction {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L) :
    ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L)) where
  domainFixed := Q.domainFixed.map
    (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.toLinearMap
  codomainVariation := Q.codomainVariation.map
    (codomainBasis B).equivFun.toLinearMap
  base := reducedMatrixEquiv B L Q.base

theorem reducedMatrix_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) (u : (V d ⧸ A) ⧸ L) :
    (reducedMatrixEquiv B L M).mulVec
        ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun u) =
      (codomainBasis B).equivFun (M u) := by
  exact LinearMap.toMatrix_mulVec_repr
    (Module.finBasis F ((V d ⧸ A) ⧸ L)) (codomainBasis B) M u

theorem reducedMatrix_sub_mulVec {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (M T : ((V d ⧸ A) ⧸ L) →ₗ[F] B) (u : (V d ⧸ A) ⧸ L) :
    (reducedMatrixEquiv B L M - reducedMatrixEquiv B L T).mulVec
        ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun u) =
      (codomainBasis B).equivFun ((M - T) u) := by
  rw [← map_sub]
  exact reducedMatrix_mulVec B L (M - T) u

private theorem mem_reduced_domain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L)
    (a : Fin (Module.finrank F ((V d ⧸ A) ⧸ L)) → F) :
    a ∈ Q.domainFixed.map
        (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.toLinearMap ↔
      (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm a ∈ Q.domainFixed := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro ha
    exact ⟨(Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm a, ha,
      (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.apply_symm_apply a⟩

private theorem mem_reduced_codomain_coordinates {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L)
    (b : Fin (Module.finrank F B) → F) :
    b ∈ Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap ↔
      (codomainBasis B).equivFun.symm b ∈ Q.codomainVariation := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hb
    exact ⟨(codomainBasis B).equivFun.symm b, hb,
      (codomainBasis B).equivFun.apply_symm_apply b⟩

theorem mem_reduced_coordinate_fibre_iff {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L)
    (M : ((V d ⧸ A) ⧸ L) →ₗ[F] B) :
    reducedMatrixEquiv B L M ∈ (reducedCoordinateRestriction Q).fibre ↔
      M ∈ Q.fibre := by
  simp only [ActualAffineRestriction.fibre, ReducedRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      have h := hD ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun u)
        ⟨u, hu, rfl⟩
      have hm : (codomainBasis B).equivFun ((M - Q.base) u) = 0 := by
        simpa only [reducedCoordinateRestriction, reducedMatrix_sub_mulVec] using h
      exact (codomainBasis B).equivFun.injective (by simpa using hm)
    · intro u
      have h := hC ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun u)
      have hm : (codomainBasis B).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap := by
        simpa only [reducedCoordinateRestriction, reducedMatrix_sub_mulVec] using h
      have hh := (mem_reduced_codomain_coordinates Q _).mp hm
      simpa only [LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      let u := (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm a
      have hu : u ∈ Q.domainFixed :=
        (mem_reduced_domain_coordinates Q a).mp ha
      have hm := reducedMatrix_sub_mulVec B L M Q.base u
      have h0 := hD u hu
      have ha' : (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun u = a :=
        (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.apply_symm_apply a
      simpa [reducedCoordinateRestriction, ha', h0] using hm
    · intro a
      let u := (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm a
      have hu := hC u
      have ha' : (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun u = a :=
        (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.apply_symm_apply a
      have hh : (codomainBasis B).equivFun ((M - Q.base) u) ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap :=
        (mem_reduced_codomain_coordinates Q _).mpr
          (by simpa only [LinearEquiv.symm_apply_apply] using hu)
      change (reducedMatrixEquiv B L M -
        reducedMatrixEquiv B L Q.base).mulVec a ∈
          Q.codomainVariation.map (codomainBasis B).equivFun.toLinearMap
      rw [← ha', reducedMatrix_sub_mulVec]
      exact hh

theorem reduced_coordinate_fibre_image {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L) :
    (reducedCoordinateRestriction Q).fibre =
      Q.fibre.image (reducedMatrixEquiv B L) := by
  ext X
  rw [Finset.mem_image]
  constructor
  · intro hX
    refine ⟨(reducedMatrixEquiv B L).symm X, ?_, by simp⟩
    exact (mem_reduced_coordinate_fibre_iff Q _).mp (by simpa using hX)
  · rintro ⟨M, hM, rfl⟩
    exact (mem_reduced_coordinate_fibre_iff Q M).mpr hM

theorem reduced_coordinate_fibre_energy {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L)
    (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ) :
    fibreEnergy (reducedCoordinateRestriction Q).fibre
        (fun X => f ((reducedMatrixEquiv B L).symm X)) =
      (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [reduced_coordinate_fibre_image]
  have hi : Set.InjOn (reducedMatrixEquiv B L :
      (((V d ⧸ A) ⧸ L) →ₗ[F] B) → BinaryMatrix
        (Module.finrank F B) (Module.finrank F ((V d ⧸ A) ⧸ L))) Q.fibre :=
    (reducedMatrixEquiv B L).injective.injOn
  simp only [fibreEnergy, Finset.sum_image hi,
    Finset.card_image_iff.mpr hi, LinearEquiv.symm_apply_apply]

theorem reduced_coordinate_order {n d : ℕ}
    {A : Submodule F (V d)} {B : Submodule F (Fin n → F)}
    {L : Submodule F (V d ⧸ A)}
    (Q : ReducedRestriction A B L) :
    (reducedCoordinateRestriction Q).order = Q.order := by
  let eU := (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun
  let eZ := (codomainBasis B).equivFun
  have hU : Module.finrank F (Q.domainFixed.map eU.toLinearMap) =
      Module.finrank F Q.domainFixed := eU.finrank_map_eq Q.domainFixed
  have hZ : Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
      Module.finrank F Q.codomainVariation :=
    eZ.finrank_map_eq Q.codomainVariation
  have hTot : Module.finrank F (Fin (Module.finrank F B) → F) =
      Module.finrank F B := eZ.finrank_eq.symm
  have hCoord : Module.finrank F
      ((Fin (Module.finrank F B) → F) ⧸
        Q.codomainVariation.map eZ.toLinearMap) +
      Module.finrank F (Q.codomainVariation.map eZ.toLinearMap) =
        Module.finrank F (Fin (Module.finrank F B) → F) :=
    (Q.codomainVariation.map eZ.toLinearMap).finrank_quotient_add_finrank
  have hTyped : Module.finrank F (B ⧸ Q.codomainVariation) +
      Module.finrank F Q.codomainVariation = Module.finrank F B :=
    Q.codomainVariation.finrank_quotient_add_finrank
  change Module.finrank F (Q.domainFixed.map eU.toLinearMap) +
      Module.finrank F
        ((Fin (Module.finrank F B) → F) ⧸
          Q.codomainVariation.map eZ.toLinearMap) =
    Module.finrank F Q.domainFixed +
      Module.finrank F (B ⧸ Q.codomainVariation)
  rw [hU]
  omega

def reducedTypedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (R : ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L))) : ReducedRestriction A B L where
  domainFixed := R.domainFixed.map
    (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm.toLinearMap
  codomainVariation := R.codomainVariation.map
    (codomainBasis B).equivFun.symm.toLinearMap
  base := (reducedMatrixEquiv B L).symm R.base

theorem reduced_coordinate_typedOfCoordinate {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (R : ActualAffineRestriction (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L))) :
    reducedCoordinateRestriction (reducedTypedOfCoordinate A B L R) = R := by
  cases R with
  | mk D C T =>
    unfold reducedTypedOfCoordinate reducedCoordinateRestriction
    congr 1
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        change (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun
          ((Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm w) ∈ D
        rw [(Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.apply_symm_apply]
        exact hw
      · intro hu
        exact ⟨(Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.symm u,
          ⟨u, hu, rfl⟩,
          (Module.finBasis F ((V d ⧸ A) ⧸ L)).equivFun.apply_symm_apply u⟩
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

def UpToReducedNormSqGlobal {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (r : ℕ) (ε : ℝ)
    (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ) : Prop :=
  ∀ Q : ReducedRestriction A B L, Q.order ≤ r →
    (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card ≤ ε

theorem reduced_global_iff_coordinate {n d r : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A))
    (f : (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ) :
    UpToReducedNormSqGlobal A B L r ε f ↔
      UpToActualNormSqGlobal r ε
        (fun X => f ((reducedMatrixEquiv B L).symm X)) := by
  constructor
  · intro hf R hR
    let Q := reducedTypedOfCoordinate A B L R
    have hQR : Q.order ≤ r := by
      rw [← reduced_coordinate_order Q, reduced_coordinate_typedOfCoordinate]
      exact hR
    have h := hf Q hQR
    rw [← reduced_coordinate_fibre_energy Q f,
      reduced_coordinate_typedOfCoordinate] at h
    exact h
  · intro hf Q hQ
    have h := hf (reducedCoordinateRestriction Q)
      (by rw [reduced_coordinate_order]; exact hQ)
    rw [reduced_coordinate_fibre_energy] at h
    exact h

theorem translate_actual_complex {n d r : ℕ} {ε : ℝ}
    (S : BinaryMatrix n d) (f : BinaryMatrix n d → ℂ)
    (hε : 0 ≤ ε) (hf : UpToActualNormSqGlobal r ε f) :
    UpToActualNormSqGlobal r ε (fun X => f (X + S)) :=
  raw_implies_actual _
    (translate_raw S f (actual_implies_raw f hε hf))

def typedLineReducedWitness {n d k : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ) :
    (((V d ⧸ A) ⧸ L) →ₗ[F] B) → ℂ :=
  fun N => typedLineP B L hL k f (T + N.comp L.mkQ)

set_option maxHeartbeats 800000 in
theorem typed_line_oneStep_A15_global {n d k : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (Fin n → F))
    (L : Submodule F (V d ⧸ A)) (hL : Module.finrank F L = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A B (k + 1) ε f) :
    UpToReducedNormSqGlobal A B L k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (typedLineReducedWitness (k := k) B L hL T f) := by
  let G : BinaryMatrix (Module.finrank F B)
      (Module.finrank F ((V d ⧸ A) ⧸ L)) → ℂ :=
    fun X => typedLineP B L hL k f
      ((lineMatrixEquiv B L hL).symm
        (rawLastColumn X (lineBaseColumn B L hL T)))
  let c := dropLastMatrix (lineMatrixEquiv B L hL T)
  have hG : UpToActualNormSqGlobal k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε) G :=
    typed_line_coordinate_witness_global A B L hL T f hε hf
  have hδ : 0 ≤ 4 * (2 : ℝ) ^ (4 * (k + 1)) * ε := by positivity
  have htr := translate_actual_complex c G hδ hG
  apply (reduced_global_iff_coordinate A B L
    (typedLineReducedWitness (k := k) B L hL T f)).mpr
  intro R hR
  have h := htr R hR
  convert h using 1
  congr 1
  funext X
  let N := (reducedMatrixEquiv B L).symm X
  have hw := typed_line_coordinate_witness_fixed_base (k := k) B L hL T N f
  rw [dropLast_lineMatrix_fixed_base] at hw
  have hN : reducedMatrixEquiv B L N = X :=
    (reducedMatrixEquiv B L).apply_symm_apply X
  rw [hN] at hw
  rw [add_comm (dropLastMatrix (lineMatrixEquiv B L hL T)) X] at hw
  change typedLineP B L hL k f (T + N.comp L.mkQ) =
    typedLineP B L hL k f
      ((lineMatrixEquiv B L hL).symm
        (rawLastColumn (X + c) (lineBaseColumn B L hL T)))
  exact hw

end
end PvNP.RealizableHardness.BinaryMatrixTypedA15ReducedGlobal
