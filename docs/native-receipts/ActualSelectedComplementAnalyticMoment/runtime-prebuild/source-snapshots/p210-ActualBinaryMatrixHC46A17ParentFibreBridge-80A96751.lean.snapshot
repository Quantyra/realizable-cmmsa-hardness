import PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
import PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel
import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier

/-! A quotient-Hom coordinate bridge for the actual ambient fibre of a
typed carrier restriction.  The domain quotient and codomain image are
transported by explicit linear equivalences.  The normalized-mean result is
for the equivalence constructed here; identifying that map with the explicit
matrix lift is a separate theorem obligation. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge

open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open BinaryMatrixActualAffine
open scoped BigOperators

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private abbrev F := ZMod 2
private abbrev V (d : Nat) := Fin d → F
private abbrev W (n : Nat) := Fin n → F

/-- The quotient-Hom coordinates of the carrier fibre are linearly
equivalent to those of its lifted actual ambient fibre.  This records the
exact quotient and codomain maps; it does not assert an energy estimate. -/
noncomputable def carrierAmbientQuotientHomEquiv {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B) :
    (((V d ⧸ A) ⧸ Q.domainFixed) →ₗ[F] Q.codomainVariation) ≃ₗ[F]
      ((V d ⧸ (Q.domainFixed.comap A.mkQ)) →ₗ[F]
        (Q.codomainVariation.map B.subtype)) := by
  let P : Submodule F (V d) := Q.domainFixed.comap A.mkQ
  have hAP : A ≤ P := by
    intro x hx
    change A.mkQ x ∈ Q.domainFixed
    simp [P]
  have hmap : P.map A.mkQ = Q.domainFixed := by
    exact Submodule.map_comap_eq_self (by
      intro y hy
      rcases Submodule.mkQ_surjective A y with ⟨x, rfl⟩
      exact ⟨x, by simpa [P] using hy, rfl⟩)
  let eD : ((V d ⧸ A) ⧸ Q.domainFixed) ≃ₗ[F] (V d ⧸ P) :=
    (LinearEquiv.ofEq _ _ (congrArg
      (fun S : Submodule F (V d ⧸ A) => (V d ⧸ A) ⧸ S) hmap.symm)).trans
      (nestedDomainEquiv A P hAP)
  let eC : Q.codomainVariation ≃ₗ[F]
      Q.codomainVariation.map B.subtype :=
    (Submodule.equivMapOfInjective B.subtype B.injective_subtype
      Q.codomainVariation).symm
  exact LinearEquiv.arrowCongr eD eC

/-- Transport the carrier fibre through its quotient-Hom coordinates and
then back to the actual ambient fibre. -/
noncomputable def carrierAmbientLiftFibreEquiv {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B) :
    {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} ≃
      {Y : BinaryMatrix n d //
        Y ∈ (liftCarrierRestriction A B T Q).fibre} := by
  exact (carrierFibreQuotientHomEquiv Q).trans
    ((carrierAmbientQuotientHomEquiv T Q).toEquiv.trans
      (actualFibreQuotientHomEquiv (liftCarrierRestriction A B T Q)).symm)

/-- The quotient-Hom fibre equivalence preserves the uniform normalized
mean exactly, for every observable on the ambient matrices. -/
theorem carrierAmbientLiftFibreEquiv_normalizedMean {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B)
    (g : BinaryMatrix n d → Real) :
    (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
      g ((carrierAmbientLiftFibreEquiv A B T Q x).1)) /
      (Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} : Real) =
    (∑ y : {Y : BinaryMatrix n d //
      Y ∈ (liftCarrierRestriction A B T Q).fibre}, g y.1) /
      (Fintype.card {Y : BinaryMatrix n d //
        Y ∈ (liftCarrierRestriction A B T Q).fibre} : Real) := by
  let e := carrierAmbientLiftFibreEquiv A B T Q
  have hs : (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
      g ((e x).1)) =
      ∑ y : {Y : BinaryMatrix n d //
        Y ∈ (liftCarrierRestriction A B T Q).fibre}, g y.1 :=
    Equiv.sum_comp e (fun y => g y.1)
  have hc : Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} =
      Fintype.card {Y : BinaryMatrix n d //
        Y ∈ (liftCarrierRestriction A B T Q).fibre} :=
    Fintype.card_congr e
  rw [hs, hc]

/-- The explicit affine lift always sends a carrier-fibre point into the
corresponding actual ambient fibre. -/
theorem liftCarrierMatrix_mem_actual_fibre {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B)
    (M : (V d ⧸ A) →ₗ[F] B) (hM : M ∈ Q.fibre) :
    liftCarrierMatrix A B T M ∈
      (liftCarrierRestriction A B T Q).fibre :=
  (liftCarrierMatrix_mem_fibre_iff A B T Q M).2 hM

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge
