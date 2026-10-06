import PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
import PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel
import PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreEvaluation
import PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier

/-! A quotient-Hom coordinate bridge for the actual ambient fibre of a
typed carrier restriction.  The domain quotient and codomain image are
transported by explicit linear equivalences.  The normalized-mean result is
for the equivalence constructed here; identifying that map with the explicit
matrix lift is a separate theorem obligation. -/

namespace PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge

open PvNP.RealizableHardness.ActualTypedCarrierAmbientBudget
open PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreModel
open PvNP.RealizableHardness.ActualBinaryMatrixHC46ActualFibreEvaluation
open PvNP.RealizableHardness.BinaryMatrixA1NestedCarrier
open BinaryMatrixActualAffine
open BinaryMatrixTypedA15Transport BinaryMatrixFourier
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
private noncomputable def carrierAmbientDomainEquiv {n d : Nat}
    (A : Submodule F (V d)) {B : Submodule F (W n)}
    (Q : CarrierRestriction A B)
    (hAP : A ≤ Q.domainFixed.comap A.mkQ)
    (hmap : (Q.domainFixed.comap A.mkQ).map A.mkQ = Q.domainFixed) :
    ((V d ⧸ A) ⧸ Q.domainFixed) ≃ₗ[F]
      (V d ⧸ (Q.domainFixed.comap A.mkQ)) :=
  (Submodule.quotEquivOfEq
    ((Q.domainFixed.comap A.mkQ).map A.mkQ) Q.domainFixed hmap).symm.trans
      (nestedDomainEquiv A (Q.domainFixed.comap A.mkQ) hAP)

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
    have hxker : x ∈ LinearMap.ker A.mkQ := by
      simpa only [Submodule.ker_mkQ] using hx
    have hxzero : A.mkQ x = 0 := LinearMap.mem_ker.mp hxker
    rw [hxzero]
    exact Q.domainFixed.zero_mem
  have hmap : P.map A.mkQ = Q.domainFixed := by
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)
  let eD : ((V d ⧸ A) ⧸ Q.domainFixed) ≃ₗ[F] (V d ⧸ P) :=
    carrierAmbientDomainEquiv A Q hAP hmap
  let eC : Q.codomainVariation ≃ₗ[F]
      Q.codomainVariation.map B.subtype :=
    Submodule.equivMapOfInjective B.subtype B.injective_subtype
      Q.codomainVariation
  exact LinearEquiv.arrowCongr eD eC

private theorem carrierAmbientDomainEquiv_symm_mkQ {n d : Nat}
    (A : Submodule F (V d)) {B : Submodule F (W n)}
    (Q : CarrierRestriction A B)
    (hAP : A ≤ Q.domainFixed.comap A.mkQ)
    (hmap : (Q.domainFixed.comap A.mkQ).map A.mkQ = Q.domainFixed)
    (v : V d) :
    (carrierAmbientDomainEquiv A Q hAP hmap).symm
        ((Q.domainFixed.comap A.mkQ).mkQ v) =
      Q.domainFixed.mkQ (A.mkQ v) := by
  let P : Submodule F (V d) := Q.domainFixed.comap A.mkQ
  let e := nestedDomainEquiv A P hAP
  have hnested : e.symm (P.mkQ v) = (P.map A.mkQ).mkQ (A.mkQ v) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change Submodule.quotientQuotientEquivQuotient A P hAP
        (Submodule.Quotient.mk (Submodule.Quotient.mk v)) =
      Submodule.Quotient.mk v
    exact (Submodule.quotientQuotientEquivQuotientAux_mk_mk
      A P hAP v).symm
  change (Submodule.quotEquivOfEq
      ((Q.domainFixed.comap A.mkQ).map A.mkQ) Q.domainFixed hmap)
      (e.symm (P.mkQ v)) = Q.domainFixed.mkQ (A.mkQ v)
  rw [hnested]
  exact Submodule.quotEquivOfEq_mk
    ((Q.domainFixed.comap A.mkQ).map A.mkQ) Q.domainFixed hmap (A.mkQ v)

private theorem carrierAmbientQuotientHomEquiv_apply_mkQ {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B)
    (N : ((V d ⧸ A) ⧸ Q.domainFixed) →ₗ[F] Q.codomainVariation)
    (v : V d) :
    (((carrierAmbientQuotientHomEquiv T Q N)
      ((Q.domainFixed.comap A.mkQ).mkQ v) :
        Q.codomainVariation.map B.subtype) : W n) =
      B.subtype (N (Q.domainFixed.mkQ (A.mkQ v))) := by
  let P : Submodule F (V d) := Q.domainFixed.comap A.mkQ
  have hAP : A ≤ P := by
    intro x hx
    change A.mkQ x ∈ Q.domainFixed
    have hxker : x ∈ LinearMap.ker A.mkQ := by
      simpa only [Submodule.ker_mkQ] using hx
    rw [LinearMap.mem_ker.mp hxker]
    exact Q.domainFixed.zero_mem
  have hmap : P.map A.mkQ = Q.domainFixed := by
    exact Submodule.map_comap_eq_self (by
      rw [Submodule.range_mkQ]
      exact le_top)
  change ((Submodule.equivMapOfInjective B.subtype B.injective_subtype
      Q.codomainVariation)
      (N ((carrierAmbientDomainEquiv A Q hAP hmap).symm (P.mkQ v)))).val = _
  rw [carrierAmbientDomainEquiv_symm_mkQ A Q hAP hmap v]
  rfl

private theorem carrierFibreQuotientHomEquiv_apply_mkQ {n d : Nat}
    {A : Submodule F (V d)} {B : Submodule F (W n)}
    (Q : CarrierRestriction A B)
    (M : (V d ⧸ A) →ₗ[F] B) (hM : M ∈ Q.fibre)
    (u : V d ⧸ A) :
    (((carrierFibreQuotientHomEquiv Q ⟨M, hM⟩)
      (Q.domainFixed.mkQ u) : Q.codomainVariation) : B) =
      ((M - Q.base) u : B) := by
  simp [carrierFibreQuotientHomEquiv, Submodule.liftQ_mkQ,
    LinearMap.codRestrict_apply]

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

/-- The quotient-Hom equivalence above is the explicit affine matrix lift,
pointwise on every carrier-fibre element. -/
theorem carrierAmbientLiftFibreEquiv_apply {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B)
    (M : (V d ⧸ A) →ₗ[F] B) (hM : M ∈ Q.fibre) :
    carrierAmbientLiftFibreEquiv A B T Q ⟨M, hM⟩ =
      ⟨liftCarrierMatrix A B T M,
        liftCarrierMatrix_mem_actual_fibre A B T Q M hM⟩ := by
  let coords : QuotientHom (liftCarrierRestriction A B T Q).domainFixed
      (liftCarrierRestriction A B T Q).codomainVariation := by
    with_unfolding_all
      exact (carrierAmbientQuotientHomEquiv T Q)
        ((carrierFibreQuotientHomEquiv Q) ⟨M, hM⟩)
  let e := actualFibreQuotientHomEquiv (liftCarrierRestriction A B T Q)
  apply e.injective
  with_unfolding_all
    change e (e.symm coords) = e ⟨liftCarrierMatrix A B T M,
      liftCarrierMatrix_mem_actual_fibre A B T Q M hM⟩
  calc
    e (e.symm coords) = coords := e.apply_symm_apply coords
    _ = e ⟨liftCarrierMatrix A B T M,
        liftCarrierMatrix_mem_actual_fibre A B T Q M hM⟩ := by
      apply LinearMap.ext
      intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro v
      apply Subtype.ext
      let P : Submodule F (V d) := Q.domainFixed.comap A.mkQ
      calc
        (((coords (P.mkQ v) : Q.codomainVariation.map B.subtype) : W n)) =
            B.subtype (((carrierFibreQuotientHomEquiv Q ⟨M, hM⟩)
              (Q.domainFixed.mkQ (A.mkQ v)) : Q.codomainVariation) : B) := by
          exact carrierAmbientQuotientHomEquiv_apply_mkQ A B T Q
            (carrierFibreQuotientHomEquiv Q ⟨M, hM⟩) v
        _ = B.subtype ((M - Q.base) (A.mkQ v) : B) := by
          rw [carrierFibreQuotientHomEquiv_apply_mkQ]
        _ = (liftCarrierMatrix A B T M -
            (liftCarrierRestriction A B T Q).base).mulVec v :=
          (liftCarrierMatrix_sub_mulVec A B T Q M v).symm
        _ = (((e ⟨liftCarrierMatrix A B T M,
            liftCarrierMatrix_mem_actual_fibre A B T Q M hM⟩)
              (P.mkQ v) : (liftCarrierRestriction A B T Q).codomainVariation) : W n) := by
          exact (actualFibreQuotientHomEquiv_apply_mkQ
            (liftCarrierRestriction A B T Q) (liftCarrierMatrix A B T M)
            (liftCarrierMatrix_mem_actual_fibre A B T Q M hM) v).symm

/-- Exact normalized-energy transport along the affine carrier lift. -/
theorem liftCarrierMatrix_normalizedMean {n d : Nat}
    (A : Submodule F (V d)) (B : Submodule F (W n))
    (T : V d →ₗ[F] W n) (Q : CarrierRestriction A B)
    (g : BinaryMatrix n d → Real) :
    (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
      g (liftCarrierMatrix A B T x.1)) /
      (Fintype.card {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre} : Real) =
    (∑ y : {Y : BinaryMatrix n d //
      Y ∈ (liftCarrierRestriction A B T Q).fibre}, g y.1) /
      (Fintype.card {Y : BinaryMatrix n d //
        Y ∈ (liftCarrierRestriction A B T Q).fibre} : Real) := by
  let e := carrierAmbientLiftFibreEquiv A B T Q
  have hpoint : ∀ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
      (e x).1 = liftCarrierMatrix A B T x.1 := by
    intro x
    exact congrArg Subtype.val
      (carrierAmbientLiftFibreEquiv_apply A B T Q x.1 x.2)
  have hsum : (∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre},
      g (liftCarrierMatrix A B T x.1)) =
      ∑ x : {M : (V d ⧸ A) →ₗ[F] B // M ∈ Q.fibre}, g ((e x).1) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hpoint x]
  rw [hsum]
  exact carrierAmbientLiftFibreEquiv_normalizedMean A B T Q g

end
end PvNP.RealizableHardness.ActualBinaryMatrixHC46A17ParentFibreBridge
