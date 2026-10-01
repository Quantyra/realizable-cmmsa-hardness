import PvNP.RealizableHardness.ActualTypedNestedAffineBase
import PvNP.RealizableHardness.ActualTypedFourierEquivNaturality

namespace PvNP.RealizableHardness.ActualTypedAmbientA14Composition

open ActualTypedNestedAffineBase ActualTypedFourierEquivNaturality
open BinaryMatrixA1NestedCarrier BinaryMatrixTypedA14Line
open BinaryMatrixTypedA14Reduced BinaryMatrixTypedA15ReducedGlobal
open BinaryMatrixNestedSelectorA1
open scoped BigOperators

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F
private abbrev NestedDomain {d : Nat} (A₂ A₁ : Submodule F (V d)) :=
  (V d ⧸ A₂) ⧸ A₁.map A₂.mkQ
private abbrev NestedCodomain {n : Nat}
    (B₁ B₂ : Submodule F (W n)) := B₁.comap B₂.subtype

/-- The flat first-carrier statistic induced by an arbitrary ambient affine
base. The ambient base is kept external to the quotient. -/
def ambientFlatStatistic {n d : Nat}
    (A₁ : Submodule F (V d)) (B₁ : Submodule F (W n))
    (f : (V d →ₗ[F] W n) → Complex)
    (T₀ : V d →ₗ[F] W n) :
    ((V d ⧸ A₁) →ₗ[F] B₁) → Complex :=
  fun M => f (T₀ + B₁.subtype.comp (M.comp A₁.mkQ))

/-- The same statistic on the actual nested quotient/comap carrier. -/
def ambientNestedStatistic {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (V d →ₗ[F] W n) → Complex)
    (T₀ : V d →ₗ[F] W n) :
    (NestedDomain A₂ A₁ →ₗ[F] NestedCodomain B₁ B₂) → Complex :=
  fun N => f (T₀ + B₂.subtype.comp
    ((0 + (B₁.comap B₂.subtype).subtype.comp
      (N.comp (A₁.map A₂.mkQ).mkQ)).comp A₂.mkQ))

/-- The nested quotient pullback is exactly the flattened ambient statistic,
with no descent condition on `T₀`. -/
theorem ambientNestedStatistic_eq_flat {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (V d →ₗ[F] W n) → Complex)
    (T₀ : V d →ₗ[F] W n) :
    ambientNestedStatistic A₂ A₁ B₁ B₂ hA hB f T₀ =
      fun N => ambientFlatStatistic A₁ B₁ f T₀
        (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N) := by
  funext N
  unfold ambientNestedStatistic ambientFlatStatistic
  have h := nestedCarrier_affine_base A₂ A₁ B₁ B₂ hA hB T₀
    (0 : (V d ⧸ A₂) →ₗ[F] B₂) N
  simpa using congrArg f h

/-- The actual typed A14 line step after an arbitrary ambient affine
first-stage update. The left side is the manuscript's typed reduced witness;
on the right the selected rank projection is computed on the genuine nested
quotient/comap carrier. -/
theorem ambient_nested_typed_A14_fixedLine {n d j : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (L : Submodule F (V d ⧸ A₁)) (hL : Module.finrank F L = 1)
    (f : (V d →ₗ[F] W n) → Complex)
    (T : V d →ₗ[F] W n)
    (S : (V d ⧸ A₂) →ₗ[F] B₂)
    (N : ((V d ⧸ A₁) ⧸ L) →ₗ[F] B₁) :
    reducedComplexRankProjection B₁ L j
      (typedLineReducedWitness (k := j) B₁ L hL 0
        (ambientFlatStatistic A₁ B₁ f
          (T + B₂.subtype.comp (S.comp A₂.mkQ)))) N =
    complexLinearMapSelectedFilter
      (Selected (L.map (nestedDomainEquiv A₂ A₁ hA).symm.toLinearMap)
        (⊤ : Submodule F (NestedCodomain B₁ B₂)))
      (fun N' => complexLinearMapRankProjection (j + 1)
        (ambientNestedStatistic A₂ A₁ B₁ B₂ hA hB f
          (T + B₂.subtype.comp (S.comp A₂.mkQ))) N')
      ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB).symm
        (N.comp L.mkQ)) := by
  let T₀ := T + B₂.subtype.comp (S.comp A₂.mkQ)
  let flat := ambientFlatStatistic A₁ B₁ f T₀
  let nested := ambientNestedStatistic A₂ A₁ B₁ B₂ hA hB f T₀
  have hpull0 := ambientNestedStatistic_eq_flat A₂ A₁ B₁ B₂ hA hB f T₀
  have hpull : nested = fun N' =>
      flat (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N') := by
    simpa [nested, flat] using hpull0
  have hproj (N' : NestedDomain A₂ A₁ →ₗ[F] NestedCodomain B₁ B₂) :
      typedComplexRankProjection A₁ B₁ (j + 1) flat
          (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N') =
        complexLinearMapRankProjection (j + 1) nested N' := by
    have htyped : ∀ M : (V d ⧸ A₁) →ₗ[F] B₁,
        typedComplexRankProjection A₁ B₁ (j + 1) flat M =
          complexLinearMapRankProjection (j + 1) flat M := by
      intro M
      simp [typedComplexRankProjection, complexLinearMapRankProjection,
        complexCarrierFourierCoeff, complexLinearMapFourierCoeff,
        Finset.sum_filter]
    rw [htyped]
    have h := nestedCarrierRankProjection (j := j + 1)
      A₂ A₁ B₁ B₂ hA hB nested N'
    simpa only [hpull, LinearEquiv.apply_symm_apply] using h
  have hfun :
      (fun N' => typedComplexRankProjection A₁ B₁ (j + 1) flat
        (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N')) =
      (fun N' => complexLinearMapRankProjection (j + 1) nested N') := by
    funext N'
    exact hproj N'
  calc
    _ = complexLinearMapSelectedFilter
        (Selected (L.map (nestedDomainEquiv A₂ A₁ hA).symm.toLinearMap)
          (⊤ : Submodule F (NestedCodomain B₁ B₂)))
        (fun N' => typedComplexRankProjection A₁ B₁ (j + 1) flat
          (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N'))
        ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB).symm
          (0 + N.comp L.mkQ)) :=
            nestedUpdatedBaseTypedA14 A₂ A₁ B₁ B₂ hA hB L hL flat 0 N
    _ = complexLinearMapSelectedFilter
        (Selected (L.map (nestedDomainEquiv A₂ A₁ hA).symm.toLinearMap)
          (⊤ : Submodule F (NestedCodomain B₁ B₂)))
        (fun N' => typedComplexRankProjection A₁ B₁ (j + 1) flat
          (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB N'))
        ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB).symm
          (N.comp L.mkQ)) := by simp
    _ = complexLinearMapSelectedFilter
        (Selected (L.map (nestedDomainEquiv A₂ A₁ hA).symm.toLinearMap)
          (⊤ : Submodule F (NestedCodomain B₁ B₂)))
        (fun N' => complexLinearMapRankProjection (j + 1) nested N')
        ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB).symm
          (N.comp L.mkQ)) := by rw [hfun]

end
end PvNP.RealizableHardness.ActualTypedAmbientA14Composition
