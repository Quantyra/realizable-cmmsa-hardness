import PvNP.RealizableHardness.BinaryMatrixA15NestedLine

namespace PvNP.RealizableHardness.BinaryMatrixA15NestedHyperplane

open BinaryMatrixTypedA15HyperplaneReducedGlobal
open BinaryMatrixTypedA15Transport BinaryMatrixFourier
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def hyperplaneCanonicalCodomain {n : ℕ}
    (B : Submodule F (W n)) (H : Submodule F B) : Submodule F (W n) :=
  H.map B.subtype

def hyperplaneCanonicalCodomainEquiv {n : ℕ}
    (B : Submodule F (W n)) (H : Submodule F B) :
    H ≃ₗ[F] hyperplaneCanonicalCodomain B H :=
  Submodule.equivMapOfInjective B.subtype Subtype.val_injective H

def hyperplaneCanonicalEquiv {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) :
    ((V d ⧸ A) →ₗ[F] H) ≃ₗ[F]
      ((V d ⧸ A) →ₗ[F] hyperplaneCanonicalCodomain B H) :=
  LinearEquiv.arrowCongr (LinearEquiv.refl F (V d ⧸ A))
    (hyperplaneCanonicalCodomainEquiv B H)

theorem hyperplaneCanonicalEquiv_apply {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B) (M : (V d ⧸ A) →ₗ[F] H)
    (u : V d ⧸ A) :
    hyperplaneCanonicalEquiv B H M u =
      hyperplaneCanonicalCodomainEquiv B H (M u) := by
  simp [hyperplaneCanonicalEquiv]

/-- Fixed-base displacement commutes with the canonical embedded
codomain, as required by the next A1 composition step. -/
theorem hyperplaneCanonical_affine_base {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B)
    (S : (V d ⧸ A) →ₗ[F] B)
    (N : (V d ⧸ A) →ₗ[F] H) :
    B.subtype.comp (S + H.subtype.comp N) =
      B.subtype.comp S +
        (hyperplaneCanonicalCodomain B H).subtype.comp
          (hyperplaneCanonicalEquiv B H N) := by
  ext u x
  rfl

def hyperplaneCanonicalRestriction {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B)
    (Q : HyperplaneReducedRestriction A B H) :
    CarrierRestriction A (hyperplaneCanonicalCodomain B H) where
  domainFixed := Q.domainFixed
  codomainVariation := Q.codomainVariation.map
    (hyperplaneCanonicalCodomainEquiv B H).toLinearMap
  base := hyperplaneCanonicalEquiv B H Q.base

theorem hyperplaneCanonical_fibre_iff {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B)
    (Q : HyperplaneReducedRestriction A B H)
    (M : (V d ⧸ A) →ₗ[F] H) :
    hyperplaneCanonicalEquiv B H M ∈
      (hyperplaneCanonicalRestriction B H Q).fibre ↔ M ∈ Q.fibre := by
  simp only [CarrierRestriction.fibre, HyperplaneReducedRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      have h := hD a ha
      change (hyperplaneCanonicalCodomainEquiv B H) ((M - Q.base) a) = 0 at h
      exact (hyperplaneCanonicalCodomainEquiv B H).injective h
    · intro u
      have h := hC u
      change (hyperplaneCanonicalCodomainEquiv B H) ((M - Q.base) u) ∈
        Q.codomainVariation.map
          (hyperplaneCanonicalCodomainEquiv B H).toLinearMap at h
      rcases h with ⟨v, hv, he⟩
      exact (hyperplaneCanonicalCodomainEquiv B H).injective he ▸ hv
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      change (hyperplaneCanonicalCodomainEquiv B H) ((M - Q.base) a) = 0
      simp [hD a ha]
    · intro u
      change (hyperplaneCanonicalCodomainEquiv B H) ((M - Q.base) u) ∈
        Q.codomainVariation.map
          (hyperplaneCanonicalCodomainEquiv B H).toLinearMap
      exact ⟨(M - Q.base) u, hC u, rfl⟩

theorem hyperplaneCanonical_order {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B)
    (Q : HyperplaneReducedRestriction A B H) :
    (hyperplaneCanonicalRestriction B H Q).order = Q.order := by
  let e := hyperplaneCanonicalCodomainEquiv B H
  have hZ : Module.finrank F (Q.codomainVariation.map e.toLinearMap) =
      Module.finrank F Q.codomainVariation := e.finrank_map_eq _
  have hTot : Module.finrank F (hyperplaneCanonicalCodomain B H) =
      Module.finrank F H := e.finrank_eq.symm
  have hCoord :=
    (Q.codomainVariation.map e.toLinearMap).finrank_quotient_add_finrank
  have hTyped := Q.codomainVariation.finrank_quotient_add_finrank
  have hCoord' : Module.finrank F ((hyperplaneCanonicalCodomain B H) ⧸
      Q.codomainVariation.map e.toLinearMap) +
      Module.finrank F (Q.codomainVariation.map e.toLinearMap) =
      Module.finrank F (hyperplaneCanonicalCodomain B H) := hCoord
  have hTyped' : Module.finrank F (H ⧸ Q.codomainVariation) +
      Module.finrank F Q.codomainVariation = Module.finrank F H := hTyped
  change Module.finrank F Q.domainFixed +
      Module.finrank F ((hyperplaneCanonicalCodomain B H) ⧸
        Q.codomainVariation.map e.toLinearMap) =
    Module.finrank F Q.domainFixed + Module.finrank F (H ⧸ Q.codomainVariation)
  rw [hZ] at hCoord'
  omega

theorem hyperplaneCanonical_fibre_image {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B)
    (Q : HyperplaneReducedRestriction A B H) :
    (hyperplaneCanonicalRestriction B H Q).fibre =
      Q.fibre.image (hyperplaneCanonicalEquiv B H) := by
  ext M
  rw [Finset.mem_image]
  constructor
  · intro hM
    refine ⟨(hyperplaneCanonicalEquiv B H).symm M, ?_, by simp⟩
    exact (hyperplaneCanonical_fibre_iff B H Q _).mp (by simpa using hM)
  · rintro ⟨N, hN, rfl⟩
    exact (hyperplaneCanonical_fibre_iff B H Q N).mpr hN

theorem hyperplaneCanonical_energy {n d : ℕ}
    {A : Submodule F (V d)} (B : Submodule F (W n))
    (H : Submodule F B)
    (Q : HyperplaneReducedRestriction A B H)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ) :
    (∑ M ∈ (hyperplaneCanonicalRestriction B H Q).fibre,
      Complex.normSq (f ((hyperplaneCanonicalEquiv B H).symm M))) /
        (hyperplaneCanonicalRestriction B H Q).fibre.card =
    (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [hyperplaneCanonical_fibre_image]
  have hi : Set.InjOn (hyperplaneCanonicalEquiv B H :
      ((V d ⧸ A) →ₗ[F] H) →
        ((V d ⧸ A) →ₗ[F] hyperplaneCanonicalCodomain B H)) Q.fibre :=
    (hyperplaneCanonicalEquiv B H).injective.injOn
  simp only [Finset.sum_image hi, Finset.card_image_iff.mpr hi,
    LinearEquiv.symm_apply_apply]

def hyperplaneReducedOfCanonical {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B)
    (R : CarrierRestriction A (hyperplaneCanonicalCodomain B H)) :
    HyperplaneReducedRestriction A B H where
  domainFixed := R.domainFixed
  codomainVariation := R.codomainVariation.map
    (hyperplaneCanonicalCodomainEquiv B H).symm.toLinearMap
  base := (hyperplaneCanonicalEquiv B H).symm R.base

theorem hyperplaneCanonical_reducedOfCanonical {n d : ℕ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B)
    (R : CarrierRestriction A (hyperplaneCanonicalCodomain B H)) :
    hyperplaneCanonicalRestriction B H
      (hyperplaneReducedOfCanonical A B H R) = R := by
  cases R with
  | mk D C T =>
    unfold hyperplaneReducedOfCanonical hyperplaneCanonicalRestriction
    congr 1
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        simpa using hw
      · intro hu
        exact ⟨(hyperplaneCanonicalCodomainEquiv B H).symm u,
          ⟨u, hu, rfl⟩, by simp⟩
    · simp

theorem typed_global_iff_hyperplaneCanonical {n d r : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B)
    (f : ((V d ⧸ A) →ₗ[F] H) → ℂ) :
    UpToHyperplaneReducedNormSqGlobal A B H r ε f ↔
      UpToTypedNormSqGlobal A (hyperplaneCanonicalCodomain B H) r ε
        (fun M => f ((hyperplaneCanonicalEquiv B H).symm M)) := by
  constructor
  · intro hf R hR
    let Q := hyperplaneReducedOfCanonical A B H R
    have hQR : Q.order ≤ r := by
      rw [← hyperplaneCanonical_order B H Q,
        hyperplaneCanonical_reducedOfCanonical]
      exact hR
    have h := hf Q hQR
    rw [← hyperplaneCanonical_energy B H Q f,
      hyperplaneCanonical_reducedOfCanonical] at h
    exact h
  · intro hf Q hQ
    have h := hf (hyperplaneCanonicalRestriction B H Q)
      (by rw [hyperplaneCanonical_order]; exact hQ)
    rw [hyperplaneCanonical_energy] at h
    exact h

/-- The hyperplane A15 witness on its canonical next A1 carrier. -/
theorem canonical_hyperplane_oneStep_A15_global {n d k : ℕ} {ε : ℝ}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (H : Submodule F B) (hH : Module.finrank F (B ⧸ H) = 1)
    (T : (V d ⧸ A) →ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A B (k + 1) ε f) :
    UpToTypedNormSqGlobal A (hyperplaneCanonicalCodomain B H) k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun M => typedHyperplaneReducedWitness (k := k) B H hH T f
        ((hyperplaneCanonicalEquiv B H).symm M)) := by
  apply (typed_global_iff_hyperplaneCanonical A B H _).mp
  exact typed_hyperplane_oneStep_A15_global A B H hH T f hε hf

end
end PvNP.RealizableHardness.BinaryMatrixA15NestedHyperplane
