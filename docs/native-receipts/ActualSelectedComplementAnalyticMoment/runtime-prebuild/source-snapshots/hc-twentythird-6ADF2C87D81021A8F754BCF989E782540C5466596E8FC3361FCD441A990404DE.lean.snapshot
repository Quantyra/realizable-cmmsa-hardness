import PvNP.RealizableHardness.BinaryMatrixA1Complex
import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier

namespace PvNP.RealizableHardness.ActualTypedFourierEquivNaturality

open BinaryMatrixA1Phase BinaryMatrixA1Complex
open BinaryMatrixA1NestedCarrier
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

private noncomputable instance linearMapFiniteType {D C : Type*}
    [Finite D] [Finite C] [AddCommGroup D] [Module F D]
    [AddCommGroup C] [Module F C] : Fintype (D →ₗ[F] C) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype C := Fintype.ofFinite C
  exact FunLike.fintype _

def mapReindexEquiv {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [AddCommGroup D'] [Module F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C) :
    (D →ₗ[F] C) ≃ₗ[F] (D' →ₗ[F] C') :=
  LinearEquiv.arrowCongr eD.symm eC.symm

def frequencyReindexEquiv {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [AddCommGroup D'] [Module F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C) :
    (C →ₗ[F] D) ≃ₗ[F] (C' →ₗ[F] D') :=
  LinearEquiv.arrowCongr eC.symm eD.symm

theorem tracePair_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup D'] [Module F D'] [Module.Finite F D'] [Module.Free F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (Y : C →ₗ[F] D) (M : D →ₗ[F] C) :
    tracePair (frequencyReindexEquiv eD eC Y)
      (mapReindexEquiv eD eC M) = tracePair Y M := by
  have hcomp :
      (frequencyReindexEquiv eD eC Y).comp
          (mapReindexEquiv eD eC M) =
        eD.symm.conj (Y.comp M) := by
    ext x
    simp [frequencyReindexEquiv, mapReindexEquiv,
      LinearEquiv.arrowCongr_apply, LinearEquiv.conj_apply]
  simp [tracePair, hcomp, LinearMap.trace_conj']

theorem frequencyReindex_rank {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [AddCommGroup D'] [Module F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (Y : C →ₗ[F] D) :
    Module.finrank F (LinearMap.range (frequencyReindexEquiv eD eC Y)) =
      Module.finrank F (LinearMap.range Y) := by
  have hpre :
      LinearMap.range (Y.comp eC.toLinearMap) = LinearMap.range Y := by
    rw [LinearMap.range_comp]
    simp
  change Module.finrank F
      (LinearMap.range
        (eD.symm.toLinearMap.comp (Y.comp eC.toLinearMap))) = _
  rw [LinearMap.range_comp, hpre]
  exact eD.symm.finrank_map_eq (LinearMap.range Y)

def complexLinearMapFourierCoeff {D C : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup C] [Module F C]
    [Fintype (D →ₗ[F] C)] [Fintype (C →ₗ[F] D)]
    (f : (D →ₗ[F] C) → Complex) (Y : C →ₗ[F] D) : Complex :=
  (∑ M : D →ₗ[F] C, f M * (traceCharacter Y M : Complex)) /
    (Fintype.card (D →ₗ[F] C) : Complex)

theorem complexLinearMapFourierCoeff_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup D'] [Module F D'] [Module.Finite F D'] [Module.Free F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    [Fintype (D →ₗ[F] C)] [Fintype (C →ₗ[F] D)]
    [Fintype (D' →ₗ[F] C')] [Fintype (C' →ₗ[F] D')]
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (f : (D →ₗ[F] C) → Complex) (Y : C →ₗ[F] D) :
    complexLinearMapFourierCoeff
        (fun M' => f ((mapReindexEquiv eD eC).symm M'))
        (frequencyReindexEquiv eD eC Y) =
      complexLinearMapFourierCoeff f Y := by
  unfold complexLinearMapFourierCoeff
  have hsum :
      (∑ M' : D' →ₗ[F] C',
        f ((mapReindexEquiv eD eC).symm M') *
          (traceCharacter (frequencyReindexEquiv eD eC Y) M' : Complex)) =
      ∑ M : D →ₗ[F] C, f M * (traceCharacter Y M : Complex) := by
    symm
    apply Fintype.sum_equiv (mapReindexEquiv eD eC).toEquiv
    intro M
    simp [traceCharacter, tracePair_reindex]
  rw [hsum]
  congr 1
  exact_mod_cast Fintype.card_congr (mapReindexEquiv eD eC).toEquiv

theorem traceCharacter_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup D'] [Module F D'] [Module.Finite F D'] [Module.Free F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (Y : C →ₗ[F] D) (M : D →ₗ[F] C) :
    traceCharacter (frequencyReindexEquiv eD eC Y)
      (mapReindexEquiv eD eC M) = traceCharacter Y M := by
  simp [traceCharacter, tracePair_reindex]

def complexLinearMapRankProjection {D C : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup C] [Module F C]
    [Fintype (D →ₗ[F] C)] [Fintype (C →ₗ[F] D)]
    (j : Nat) (f : (D →ₗ[F] C) → Complex) (M : D →ₗ[F] C) : Complex :=
  ∑ Y : C →ₗ[F] D,
    if Module.finrank F (LinearMap.range Y) = j then
      complexLinearMapFourierCoeff f Y * (traceCharacter Y M : Complex)
    else 0

theorem complexLinearMapRankProjection_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup D'] [Module F D'] [Module.Finite F D'] [Module.Free F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    [Fintype (D →ₗ[F] C)] [Fintype (C →ₗ[F] D)]
    [Fintype (D' →ₗ[F] C')] [Fintype (C' →ₗ[F] D')]
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (j : Nat) (f : (D →ₗ[F] C) → Complex) (M : D →ₗ[F] C) :
    complexLinearMapRankProjection j
        (fun M' => f ((mapReindexEquiv eD eC).symm M'))
        (mapReindexEquiv eD eC M) =
      complexLinearMapRankProjection j f M := by
  unfold complexLinearMapRankProjection
  symm
  apply Fintype.sum_equiv (frequencyReindexEquiv eD eC).toEquiv
  intro Y
  rw [complexLinearMapFourierCoeff_reindex eD eC f Y,
    traceCharacter_reindex eD eC Y M]
  simp [frequencyReindex_rank]

def complexLinearMapSelectedFilter {D C : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup C] [Module F C]
    [Fintype (D →ₗ[F] C)] [Fintype (C →ₗ[F] D)]
    (P : (C →ₗ[F] D) → Prop)
    (f : (D →ₗ[F] C) → Complex) (M : D →ₗ[F] C) : Complex :=
  ∑ Y : C →ₗ[F] D,
    if P Y then complexLinearMapFourierCoeff f Y *
      (traceCharacter Y M : Complex) else 0

theorem complexLinearMapSelectedFilter_reindex {D D' C C' : Type*}
    [AddCommGroup D] [Module F D] [Module.Finite F D] [Module.Free F D]
    [AddCommGroup D'] [Module F D'] [Module.Finite F D'] [Module.Free F D']
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    [Fintype (D →ₗ[F] C)] [Fintype (C →ₗ[F] D)]
    [Fintype (D' →ₗ[F] C')] [Fintype (C' →ₗ[F] D')]
    (eD : D' ≃ₗ[F] D) (eC : C' ≃ₗ[F] C)
    (P : (C →ₗ[F] D) → Prop) (P' : (C' →ₗ[F] D') → Prop)
    (hP : ∀ Y, P' (frequencyReindexEquiv eD eC Y) ↔ P Y)
    (f : (D →ₗ[F] C) → Complex) (M : D →ₗ[F] C) :
    complexLinearMapSelectedFilter P'
        (fun M' => f ((mapReindexEquiv eD eC).symm M'))
        (mapReindexEquiv eD eC M) =
      complexLinearMapSelectedFilter P f M := by
  unfold complexLinearMapSelectedFilter
  symm
  apply Fintype.sum_equiv (frequencyReindexEquiv eD eC).toEquiv
  intro Y
  rw [complexLinearMapFourierCoeff_reindex eD eC f Y,
    traceCharacter_reindex eD eC Y M]
  simp [hP]

theorem nestedCarrierFourierCoeff {n d : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (NestedDomain A₂ A₁ →ₗ[F] NestedCodomain B₁ B₂) → Complex)
    (Y : NestedCodomain B₁ B₂ →ₗ[F] NestedDomain A₂ A₁) :
    complexLinearMapFourierCoeff
        (fun M' => f ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB).symm M'))
        (frequencyReindexEquiv
          (nestedDomainEquiv A₂ A₁ hA).symm
          (nestedCodomainEquiv B₁ B₂ hB).symm Y) =
      complexLinearMapFourierCoeff f Y := by
  simpa [mapReindexEquiv, frequencyReindexEquiv,
    nestedCarrierEquiv, nestedDomainEquiv, nestedCodomainEquiv] using
      complexLinearMapFourierCoeff_reindex
        (nestedDomainEquiv A₂ A₁ hA).symm
        (nestedCodomainEquiv B₁ B₂ hB).symm f Y

theorem nestedCarrierRankProjection {n d j : Nat}
    (A₂ A₁ : Submodule F (V d))
    (B₁ B₂ : Submodule F (W n))
    (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂)
    (f : (NestedDomain A₂ A₁ →ₗ[F] NestedCodomain B₁ B₂) → Complex)
    (M : NestedDomain A₂ A₁ →ₗ[F] NestedCodomain B₁ B₂) :
    complexLinearMapRankProjection j
        (fun M' => f ((nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB).symm M'))
        (nestedCarrierEquiv A₂ A₁ B₁ B₂ hA hB M) =
      complexLinearMapRankProjection j f M := by
  simpa [mapReindexEquiv, frequencyReindexEquiv,
    nestedCarrierEquiv, nestedDomainEquiv, nestedCodomainEquiv] using
      complexLinearMapRankProjection_reindex
        (nestedDomainEquiv A₂ A₁ hA).symm
        (nestedCodomainEquiv B₁ B₂ hB).symm j f M

theorem complexCarrierFourierCoeff_reindex {n d n' d' : Nat}
    (A : Submodule F (V d)) (A' : Submodule F (V d'))
    (B : Submodule F (W n)) (B' : Submodule F (W n'))
    (eD : (V d' ⧸ A') ≃ₗ[F] (V d ⧸ A))
    (eC : B' ≃ₗ[F] B)
    (f : ((V d ⧸ A) →ₗ[F] B) → Complex)
    (Y : B →ₗ[F] (V d ⧸ A)) :
    complexCarrierFourierCoeff A' B'
        (fun M' => f ((mapReindexEquiv eD eC).symm M'))
        (frequencyReindexEquiv eD eC Y) =
      complexCarrierFourierCoeff A B f Y := by
  simpa [complexCarrierFourierCoeff, complexLinearMapFourierCoeff] using
    complexLinearMapFourierCoeff_reindex eD eC f Y

end
end PvNP.RealizableHardness.ActualTypedFourierEquivNaturality
