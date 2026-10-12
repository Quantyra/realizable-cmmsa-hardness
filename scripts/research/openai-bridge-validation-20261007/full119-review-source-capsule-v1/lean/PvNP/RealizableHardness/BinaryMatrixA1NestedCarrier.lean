import PvNP.RealizableHardness.BinaryMatrixA1TypedFourier
import Mathlib.LinearAlgebra.Isomorphisms

namespace PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier

set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : ℕ) := Fin d → F
private abbrev W (n : ℕ) := Fin n → F

def nestedDomainEquiv {d : ℕ} (A₂ A₁ : Submodule F (V d))
    (hA : A₂ ≤ A₁) :
    ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) ≃ₗ[F] (V d ⧸ A₁) :=
  Submodule.quotientQuotientEquivQuotient A₂ A₁ hA

def nestedCodomainEquiv {n : ℕ} (B₁ B₂ : Submodule F (W n))
    (hB : B₁ ≤ B₂) :
    (B₁.comap B₂.subtype) ≃ₗ[F] B₁ where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, hB y.property⟩, y.property⟩
  left_inv x := by rfl
  right_inv y := by rfl
  map_add' x y := by rfl
  map_smul' c x := by rfl

def nestedCarrierEquiv {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂) :
    (((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype))
      ≃ₗ[F] ((V d ⧸ A₁) →ₗ[F] B₁) :=
  LinearEquiv.arrowCongr (nestedDomainEquiv A₂ A₁ hA)
    (nestedCodomainEquiv B₁ B₂ hB)

theorem nestedCarrier_apply_mk {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype))
    (v : V d) :
    (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) (A₁.mkQ v) =
      nestedCodomainEquiv B₁ B₂ hB
        (N ((A₁.map A₂.mkQ).mkQ (A₂.mkQ v))) := by
  simp only [nestedCarrierEquiv, LinearEquiv.arrowCongr_apply]
  congr 1

/-- The exact manuscript A1 affine base/displacement law before applying
either hybrid filter. -/
theorem nestedCarrier_affine_base {n d : ℕ}
    (A₂ A₁ : Submodule F (V d)) (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F] (B₁.comap B₂.subtype)) :
    T + B₂.subtype.comp
      ((S + (B₁.comap B₂.subtype).subtype.comp
        (N.comp (A₁.map A₂.mkQ).mkQ)).comp A₂.mkQ) =
      (T + B₂.subtype.comp (S.comp A₂.mkQ)) +
        B₁.subtype.comp
          ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N).comp A₁.mkQ) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [nestedCarrier_apply_mk A₂ A₁ B₁ B₂ hA hB N v]
  simp [map_add, add_assoc, nestedCodomainEquiv]

end
end PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
