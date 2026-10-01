import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier

namespace PvNP.RealizableHardness.ActualTypedNestedAffineBase

open BinaryMatrixA1NestedCarrier
open scoped BigOperators

set_option autoImplicit false
noncomputable section

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d -> F
private abbrev W (n : Nat) := Fin n -> F

/-- Pull an ambient complex statistic back to the first typed carrier at an
arbitrary ambient affine base. -/
def firstCarrierAmbientPullback {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (f : (V d →ₗ[F] W n) → Complex) (T : V d →ₗ[F] W n)
    (M : (V d ⧸ A) →ₗ[F] B) : Complex :=
  f (T + B.subtype.comp (M.comp A.mkQ))

/-- Ambient affine pullback along the actual second-stage nested carrier. -/
def nestedAmbientPullback {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (V d →ₗ[F] W n) → Complex)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (N : ((V d ⧸ A₂) ⧸ A₁.map A₂.mkQ) →ₗ[F]
      (B₁.comap B₂.subtype)) : Complex :=
  f (T + B₂.subtype.comp
    ((S + (B₁.comap B₂.subtype).subtype.comp
      (N.comp (A₁.map A₂.mkQ).mkQ)).comp A₂.mkQ))

/-- The corresponding flattened ambient pullback.  This keeps the initial
ambient base external; no quotient-descent hypothesis on it is needed. -/
def flattenedAmbientPullback {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (V d →ₗ[F] W n) → Complex)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (M : (V d ⧸ A₁) →ₗ[F] B₁) : Complex :=
  f ((T + B₂.subtype.comp (S.comp A₂.mkQ)) +
    B₁.subtype.comp (M.comp A₁.mkQ))

/-- The actual A1 nested-carrier affine identity, after applying an arbitrary
ambient statistic.  It identifies the complete pulled-back function, for
every second-stage map, with the same function on the flattened carrier. -/
theorem nestedAmbientPullback_eq_flattened {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (V d →ₗ[F] W n) → Complex)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂) :
    (fun N => nestedAmbientPullback A₂ A₁ B₁ B₂ hA hB f T S N) =
    (fun N => flattenedAmbientPullback A₂ A₁ B₁ B₂ hA hB f T S
      (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N)) := by
  funext N
  unfold nestedAmbientPullback flattenedAmbientPullback
  exact congrArg f
    (nestedCarrier_affine_base A₂ A₁ B₁ B₂ hA hB T S N)

/-- A function-level version of the same pullback identity, exposing the
first-stage statistic `g(M) = f(T + B₂.subtype ∘ M ∘ A₂.mkQ)` explicitly. -/
theorem firstCarrierPullback_eq_flattened {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (V d →ₗ[F] W n) → Complex)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂) :
    (fun N => firstCarrierAmbientPullback A₂ B₂ f T
      (S + (B₁.comap B₂.subtype).subtype.comp
        (N.comp (A₁.map A₂.mkQ).mkQ))) =
    (fun N => flattenedAmbientPullback A₂ A₁ B₁ B₂ hA hB f T S
      (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N)) := by
  funext N
  unfold firstCarrierAmbientPullback flattenedAmbientPullback
  exact congrArg f
    (nestedCarrier_affine_base A₂ A₁ B₁ B₂ hA hB T S N)

end
end PvNP.RealizableHardness.ActualTypedNestedAffineBase
