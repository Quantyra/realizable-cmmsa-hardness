import PvNP.RealizableHardness.BinaryMatrixA15BaseCase

namespace PvNP.RealizableHardness.BinaryMatrixA15NestedLine

open BinaryMatrixA1NestedCarrier BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixTypedA15Transport BinaryMatrixFourier
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def lineCanonicalEquiv {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁) :
    (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) ≃ₗ[F]
      ((V d ⧸ A₁) →ₗ[F] B) :=
  LinearEquiv.arrowCongr (nestedDomainEquiv A₂ A₁ hA) (LinearEquiv.refl F B)

def lineCanonicalRestriction {n d : ℕ}
    {A₂ A₁ : Submodule F (V d)} (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Q : ReducedRestriction A₂ B (A₁.map A₂.mkQ)) :
    CarrierRestriction A₁ B where
  domainFixed := Q.domainFixed.map (nestedDomainEquiv A₂ A₁ hA).toLinearMap
  codomainVariation := Q.codomainVariation
  base := lineCanonicalEquiv A₂ A₁ B hA Q.base

theorem lineCanonicalEquiv_apply {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (M : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B)
    (u : V d ⧸ A₁) :
    lineCanonicalEquiv A₂ A₁ B hA M u =
      M ((nestedDomainEquiv A₂ A₁ hA).symm u) := by
  simp [lineCanonicalEquiv]

theorem lineCanonicalEquiv_sub_apply {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (M T : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B)
    (u : V d ⧸ A₁) :
    (lineCanonicalEquiv A₂ A₁ B hA M -
      lineCanonicalEquiv A₂ A₁ B hA T) u =
        (M - T) ((nestedDomainEquiv A₂ A₁ hA).symm u) := by
  rw [← map_sub, lineCanonicalEquiv_apply]

theorem lineCanonical_fibre_iff {n d : ℕ}
    {A₂ A₁ : Submodule F (V d)} (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Q : ReducedRestriction A₂ B (A₁.map A₂.mkQ))
    (M : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) :
    lineCanonicalEquiv A₂ A₁ B hA M ∈
      (lineCanonicalRestriction B hA Q).fibre ↔ M ∈ Q.fibre := by
  simp only [CarrierRestriction.fibre, ReducedRestriction.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hD, hC⟩
    constructor
    · intro a ha
      have h := hD (nestedDomainEquiv A₂ A₁ hA a) ⟨a, ha, rfl⟩
      simpa only [lineCanonicalRestriction, lineCanonicalEquiv_sub_apply,
        LinearEquiv.symm_apply_apply] using h
    · intro v
      have h := hC (nestedDomainEquiv A₂ A₁ hA v)
      simpa only [lineCanonicalRestriction, lineCanonicalEquiv_sub_apply,
        LinearEquiv.symm_apply_apply] using h
  · rintro ⟨hD, hC⟩
    constructor
    · intro u hu
      obtain ⟨a, ha, rfl⟩ := hu
      change (lineCanonicalEquiv A₂ A₁ B hA M -
        lineCanonicalEquiv A₂ A₁ B hA Q.base)
          (nestedDomainEquiv A₂ A₁ hA a) = 0
      rw [lineCanonicalEquiv_sub_apply]
      simpa using hD a ha
    · intro u
      change (lineCanonicalEquiv A₂ A₁ B hA M -
        lineCanonicalEquiv A₂ A₁ B hA Q.base) u ∈ Q.codomainVariation
      rw [lineCanonicalEquiv_sub_apply]
      exact hC _

theorem lineCanonical_order {n d : ℕ}
    {A₂ A₁ : Submodule F (V d)} (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Q : ReducedRestriction A₂ B (A₁.map A₂.mkQ)) :
    (lineCanonicalRestriction B hA Q).order = Q.order := by
  change Module.finrank F (Q.domainFixed.map
      (nestedDomainEquiv A₂ A₁ hA).toLinearMap) +
      Module.finrank F (B ⧸ Q.codomainVariation) =
    Module.finrank F Q.domainFixed +
      Module.finrank F (B ⧸ Q.codomainVariation)
  rw [(nestedDomainEquiv A₂ A₁ hA).finrank_map_eq]

theorem lineCanonical_fibre_image {n d : ℕ}
    {A₂ A₁ : Submodule F (V d)} (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Q : ReducedRestriction A₂ B (A₁.map A₂.mkQ)) :
    (lineCanonicalRestriction B hA Q).fibre =
      Q.fibre.image (lineCanonicalEquiv A₂ A₁ B hA) := by
  ext M
  rw [Finset.mem_image]
  constructor
  · intro hM
    refine ⟨(lineCanonicalEquiv A₂ A₁ B hA).symm M, ?_, by simp⟩
    exact (lineCanonical_fibre_iff B hA Q _).mp (by simpa using hM)
  · rintro ⟨N, hN, rfl⟩
    exact (lineCanonical_fibre_iff B hA Q N).mpr hN

theorem lineCanonical_energy {n d : ℕ}
    {A₂ A₁ : Submodule F (V d)} (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (Q : ReducedRestriction A₂ B (A₁.map A₂.mkQ))
    (f : (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) → ℂ) :
    (∑ M ∈ (lineCanonicalRestriction B hA Q).fibre,
      Complex.normSq (f ((lineCanonicalEquiv A₂ A₁ B hA).symm M))) /
        (lineCanonicalRestriction B hA Q).fibre.card =
    (∑ M ∈ Q.fibre, Complex.normSq (f M)) / Q.fibre.card := by
  rw [lineCanonical_fibre_image]
  have hi : Set.InjOn (lineCanonicalEquiv A₂ A₁ B hA :
      (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) →
        ((V d ⧸ A₁) →ₗ[F] B)) Q.fibre :=
    (lineCanonicalEquiv A₂ A₁ B hA).injective.injOn
  simp only [Finset.sum_image hi, Finset.card_image_iff.mpr hi,
    LinearEquiv.symm_apply_apply]

def lineReducedOfCanonical {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (R : CarrierRestriction A₁ B) :
    ReducedRestriction A₂ B (A₁.map A₂.mkQ) where
  domainFixed := R.domainFixed.map (nestedDomainEquiv A₂ A₁ hA).symm.toLinearMap
  codomainVariation := R.codomainVariation
  base := (lineCanonicalEquiv A₂ A₁ B hA).symm R.base

theorem lineCanonical_reducedOfCanonical {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (R : CarrierRestriction A₁ B) :
    lineCanonicalRestriction B hA (lineReducedOfCanonical A₂ A₁ B hA R) = R := by
  cases R with
  | mk D C T =>
    unfold lineReducedOfCanonical lineCanonicalRestriction
    congr 1
    · ext u
      simp only [Submodule.mem_map]
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        simpa using hw
      · intro hu
        exact ⟨(nestedDomainEquiv A₂ A₁ hA).symm u,
          ⟨u, hu, rfl⟩, by simp⟩
    · simp

theorem typed_global_iff_lineCanonical {n d r : ℕ} {ε : ℝ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (f : (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] B) → ℂ) :
    UpToReducedNormSqGlobal A₂ B (A₁.map A₂.mkQ) r ε f ↔
      UpToTypedNormSqGlobal A₁ B r ε
        (fun M => f ((lineCanonicalEquiv A₂ A₁ B hA).symm M)) := by
  constructor
  · intro hf R hR
    let Q := lineReducedOfCanonical A₂ A₁ B hA R
    have hQR : Q.order ≤ r := by
      rw [← lineCanonical_order B hA Q, lineCanonical_reducedOfCanonical]
      exact hR
    have h := hf Q hQR
    rw [← lineCanonical_energy B hA Q f,
      lineCanonical_reducedOfCanonical] at h
    exact h
  · intro hf Q hQ
    have h := hf (lineCanonicalRestriction B hA Q)
      (by rw [lineCanonical_order]; exact hQ)
    rw [lineCanonical_energy] at h
    exact h

/-- The line A15 witness reindexed to the canonical next A1 carrier.
This is the quantified globalness handoff needed by the next peel. -/
theorem canonical_line_oneStep_A15_global {n d k : ℕ} {ε : ℝ}
    (A₂ A₁ : Submodule F (V d)) (B : Submodule F (W n))
    (hA : A₂ ≤ A₁)
    (hL : Module.finrank F (A₁.map A₂.mkQ) = 1)
    (T : (V d ⧸ A₂) →ₗ[F] B)
    (f : ((V d ⧸ A₂) →ₗ[F] B) → ℂ)
    (hε : 0 ≤ ε)
    (hf : UpToTypedNormSqGlobal A₂ B (k + 1) ε f) :
    UpToTypedNormSqGlobal A₁ B k
      (4 * (2 : ℝ) ^ (4 * (k + 1)) * ε)
      (fun M => BinaryMatrixTypedA15ReducedGlobal.typedLineReducedWitness
        (k := k) B (A₁.map A₂.mkQ) hL T f
          ((lineCanonicalEquiv A₂ A₁ B hA).symm M)) := by
  apply (typed_global_iff_lineCanonical A₂ A₁ B hA _).mp
  exact BinaryMatrixTypedA15ReducedGlobal.typed_line_oneStep_A15_global
    A₂ B (A₁.map A₂.mkQ) hL T f hε hf

end
end PvNP.RealizableHardness.BinaryMatrixA15NestedLine
